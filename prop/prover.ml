open Z3
open Solver
open Sugar
open Syntax
open ZUtilsConfig

(* Constructors stay in [Portfolio]; a match on a [check_sat] result resolves
   them from the scrutinee's type. *)
type smt_result = Portfolio.smt_result
type prover = { ax_sys : laxiom_system; ctx : context }

let mk_prover () = { ctx = mk_context []; ax_sys = Axiom.emp }
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

let update_axioms axioms =
  let p = get_prover () in
  _prover := Some { p with ax_sys = Axiom.add_laxioms p.ax_sys axioms }

let serialize (ctx : context) (exprs : Expr.expr list) : string =
  let solver = mk_solver ctx None in
  Solver.add solver exprs;
  Solver.to_string solver

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
  let wrap ?(mbqi_only = false) body =
    let mq =
      if mbqi_only then
        "(set-option :smt.ematching false)\n(set-option :smt.mbqi true)\n"
      else ""
    in
    Printf.sprintf
      "%s(set-option :timeout %d)\n\
       %s%s\n\
       (check-sat)\n\
       (get-info :reason-unknown)\n"
      mq timeout rlimit_opt body
  in
  [
    { Portfolio.label = "axiom"; query = wrap axiom_body };
    {
      Portfolio.label = "axiom_mbqi-only";
      query = wrap ~mbqi_only:true axiom_body;
    };
  ]

let select_axioms prop =
  let { ax_sys; _ } = get_prover () in
  Axiom.find_axioms ax_sys prop

let all_axioms () =
  let { ax_sys; _ } = get_prover () in
  Axiom.all_axioms ax_sys

let check_sat ~axioms prop =
  incr query_counter;
  let { ctx; _ } = get_prover () in
  let z3_axioms = List.map (fun (_, p) -> Propencoding.to_z3 ctx p) axioms in
  let query = Propencoding.to_z3 ctx prop in
  let _ =
    ZUtilsLog.queries @@ fun _ ->
    Pp.printf "@{<bold>QUERY:@}\n%s\n" (Expr.to_string query)
  in
  let body = serialize ctx (z3_axioms @ [ query ]) in
  let entries = portfolio_entries body in
  dump_queries entries;
  let time_t, (res, winner) = Sugar.clock (fun () -> Portfolio.solve entries) in
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

(* z3's [:reason-unknown] → which knob to raise to move the verdict. *)
let coercion_hint = function
  | Some r when String.starts_with ~prefix:"max. resource" r ->
      "raise rlimit first, then debug the query"
  | Some ("timeout" | "canceled") ->
      "raise the prover timeout first, then debug the query"
  | Some r -> Printf.sprintf "z3 reason-unknown: %s" r
  | None -> "z3 gave no reason-unknown"
