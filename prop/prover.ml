open Z3
open Solver
open Sugar
open Syntax
open ZUtilsConfig
open Zdatatype

type smt_result = Portfolio.smt_result =
  | SmtSat
  | SmtUnsat
  | Unknown of string option

type valid_result = SmtValid | SmtInvalid | Unknown of string option
type prover = { ax_sys : laxiom_system; ctx : context }

let layout_smt_result = function
  | SmtSat model ->
      ( _log "model" @@ fun _ ->
        Printf.printf "model:\n%s\n" (layout_model model) );
      "sat"
  | SmtUnsat -> "unsat"
  | Timeout -> "timeout"

type prover = {
  ax_sys : laxiom_system;
  ctx : context;
  solver : solver;
  goal : goal;
}

let _mk_prover timeout_bound =
  let ctx =
    mk_context
      [
        ("model", "true");
        ("proof", "false");
        ("timeout", string_of_int timeout_bound);
      ]
  in
  let () = Dtencoding.register_all_for_ctx ctx Z3aux.tp_to_sort in
  let solver = mk_solver ctx None in
  let goal = mk_goal ctx true false false in
  let ax_sys = Axiom.emp in
  { ctx; ax_sys; solver; goal }

let mk_prover () = _mk_prover (get_prover_timeout_bound ())
let _prover : prover option ref = ref None

let get_prover () =
  match !_prover with
  | Some p -> p
  | None ->
      let p = mk_prover () in
      let () = _prover := Some p in
      p

let query_counter = ref 0

(* [None] emits no [:rlimit], leaving z3's own default. *)
let _rlimit : int option ref = ref None

let set_z3_rlimit (rlimit : int option) =
  Option.iter
    (fun n ->
      if n <= 0 then
        failwith (Printf.sprintf "z3 rlimit must be positive, got %d" n))
    rlimit;
  _rlimit := rlimit

let _timeout : int option ref = ref None

let set_z3_timeout (timeout : int option) =
  Option.iter
    (fun n ->
      if n <= 0 then
        failwith (Printf.sprintf "z3 timeout must be positive, got %d" n))
    timeout;
  _timeout := timeout

let query_counter = ref 0

let set_z3_rlimit rlimit =
  Z3.Params.update_param_value (get_ctx ()) "rlimit" (string_of_int rlimit)

let set_z3_timeout (timeout : int option) =
  match timeout with
  | None -> ()
  | Some t ->
      Z3.Params.update_param_value (get_ctx ()) "timeout" (string_of_int t)

let update_axioms axioms =
  let p = get_prover () in
  _prover := Some { p with ax_sys = Axiom.add_laxioms p.ax_sys axioms }

let serialize (ctx : context) (exprs : Expr.expr list) : string =
  let solver = mk_solver ctx None in
  Solver.add solver exprs;
  Solver.to_string solver

let declares_datatype body =
  String.split_on_char '\n' body
  |> List.exists (String.starts_with ~prefix:"(declare-datatype")

let dump_queries entries =
  ZUtilsLog.dump_smt @@ fun _ ->
  List.iter
    (fun { Portfolio.label; query } ->
      let path =
        Filename.concat
          (Filename.get_temp_dir_name ())
          (Printf.sprintf "zutils_query_%i_%i_%s.smt2" (Unix.getpid ())
             !query_counter label)
      in
      Out_channel.with_open_text path (fun oc -> output_string oc query);
      Printf.eprintf "Dumped SMT query to %s\n" path)
    entries

(* The queries raced for one [check_sat] *)
let portfolio_entries axiom_body : Portfolio.entry list =
  let timeout =
    match !_timeout with Some t -> t | None -> get_prover_timeout_bound ()
  in
  if timeout <= 0 then
    failwith (Printf.sprintf "prover timeout must be positive, got %d" timeout);
  let rlimit_opt =
    match !_rlimit with
    | Some r -> Printf.sprintf "(set-option :rlimit %d)\n" r
    | None -> ""
  in
  let wrap ?(dt_eager = false) ?(mbqi_only = false) body =
    let dt = if dt_eager then "(set-option :smt.dt_lazy_splits 0)\n" else "" in
    let mq =
      if mbqi_only then
        "(set-option :smt.ematching false)\n(set-option :smt.mbqi true)\n"
      else ""
    in
    Printf.sprintf
      "%s%s(set-option :timeout %d)\n\
       %s%s\n\
       (check-sat)\n\
       (get-info :reason-unknown)\n"
      dt mq timeout rlimit_opt body
  in
  (* [dt_lazy_splits] only steers datatype case splits, so a body without a
     datatype would race a copy of [axiom]. *)
  let dt_eager =
    if declares_datatype axiom_body then
      [
        {
          Portfolio.label = "axiom_dt-eager";
          query = wrap ~dt_eager:true axiom_body;
        };
      ]
    else []
  in
  ({ Portfolio.label = "axiom"; query = wrap axiom_body } :: dt_eager)
  @ [
      {
        Portfolio.label = "axiom_mbqi-only";
        query = wrap ~mbqi_only:true axiom_body;
      };
    ]

let select_axioms prop =
  let { ax_sys; _ } = get_prover () in
  Axiom.find_axioms ax_sys prop

let select_axioms (task, prop) =
  let { ax_sys; _ } = get_prover () in
  Axiom.find_axioms ax_sys (task, prop)

let check_sat ~axioms (_task, prop) =
  incr query_counter;
  let { goal; solver; ctx; _ } = get_prover () in
  let z3_axioms = List.map (Propencoding.to_z3 ctx) axioms in
  let query = Propencoding.to_z3 ctx prop in
  let _ =
    ZUtilsLog.queries @@ fun _ ->
    Pp.printf "@{<bold>QUERY:@}\n%s\n" (Expr.to_string query)
  in
  Goal.reset goal;
  Goal.add goal (z3_axioms @ [ query ]);
  let _ =
    _log_queries @@ fun _ ->
    Pp.printf "@{<bold>Goal:@}\n%s\n" (Goal.to_string goal)
  in
  (* let goal = Goal.simplify goal None in *)
  (* let _ = *)
  (*   _log_queries @@ fun _ -> *)
  (*   Pp.printf "@{<bold>Simplifid Goal:@}\n%s\n" (Goal.to_string goal) *)
  (* in *)
  Goal.add goal z3_axioms;
  Solver.reset solver;
  Solver.add solver (get_formulas goal);
  (match Sys.getenv_opt "ZUTILS_DUMP_SMT" with
   | None -> ()
   | Some _ ->
       let idx = !query_counter in
       let path =
         Filename.concat (Filename.get_temp_dir_name ())
           (Printf.sprintf "zutils_query_%i.smt2" idx)
       in
       let oc = open_out path in
       output_string oc (Solver.to_string solver);
       output_string oc "\n(check-sat)\n";
       close_out oc;
       Printf.eprintf "Dumped SMT query to %s\n" path);
  let time_t, res = Sugar.clock (fun () -> handle_sat_result solver) in
  let () =
    ZUtilsLog.stat @@ fun _ ->
    Pp.printf
      "@{<bold>Z3 Solving time [q%i]: %.2f (%s, %i asserts, winner:%s)@}\n"
      !query_counter time_t
      (Portfolio.layout_smt_result res)
      (1 + List.length z3_axioms)
      (match winner with Some l -> l | None -> "-")
  in
  res

let check_sat_bool ~axioms (task, prop) =
  let res = check_sat ~axioms (task, prop) in
  let () =
    _log_queries @@ fun _ ->
    Pp.printf "@{<bold>SAT(%s): @} %s\n" (layout_smt_result res)
      (Front.layout_prop prop)
  in
  let res =
    match res with
    | SmtUnsat -> false
    | SmtSat model ->
        ( _log "model" @@ fun _ ->
          Printf.printf "model:\n%s\n" (layout_model model) );
        true
    | Timeout ->
        (_log_queries @@ fun _ -> Pp.printf "@{<bold>SMTTIMEOUT@}\n");
        false
  in
  res

let record_nondecisive ~reason ~coerced_to =
  ZUtilsLog.queries @@ fun () ->
  Printf.eprintf
    "[non-decisive Z3 verdict] q%i: timeout/unknown coerced to %s; %s.\n"
    !query_counter coerced_to (coercion_hint reason)

let check_valid loc query =
  match check_sat loc (smart_not query) with
  | SmtUnsat -> SmtValid
  | SmtSat -> SmtInvalid
  | Unknown reason -> Unknown reason

(** Unsat means true; otherwise means false *)
let check_valid ~axioms (task, prop) =
  let () = _store_input (task, prop) in
  (* let () = *)
  (*   Printf.printf "input:\n%s\n" *)
  (*     (Sexplib.Sexp.to_string @@ sexp_of_prop Nt.sexp_of_nt (Not prop)) *)
  (* in *)
  match check_sat ~axioms (task, Not prop) with
  | SmtUnsat -> true
  | SmtSat model ->
      ( _log "model" @@ fun _ ->
        Printf.printf "model:\n%s\n" (layout_model model) );
      false
  | Timeout ->
      (_log_queries @@ fun _ -> Pp.printf "@{<bold>SMTTIMEOUT@}\n");
      false
