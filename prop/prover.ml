open Z3
open Solver
open Goal
open Sugar
open Syntax
open ZUtilsConfig

let _log_queries = _log "queries"
let _log_dump_smt = _log "dump_smt"
let _log_stat = _log "stat"

(* Constructors re-exported so callers use [Prover.SmtUnsat], not [Portfolio.*]. *)
type smt_result = Portfolio.smt_result =
  | SmtSat
  | SmtUnsat
  | Unknown of string option

let layout_smt_result = function
  | SmtSat -> "sat"
  | SmtUnsat -> "unsat"
  | Unknown None -> "unknown"
  | Unknown (Some r) -> Printf.sprintf "unknown(%s)" r

type prover = { ax_sys : laxiom_system; env : Dtencoding.z3_env }

let mk_prover () =
  let ctx = mk_context [ ("model", "true"); ("proof", "false") ] in
  let env = Dtencoding.register_all_for_ctx ctx Z3aux.tp_to_sort in
  let ax_sys = Axiom.emp in
  { env; ax_sys }

let _prover : prover option ref = ref None

let get_prover () =
  match !_prover with
  | Some p -> p
  | None ->
      let p = mk_prover () in
      let () = _prover := Some p in
      p

let query_counter = ref 0

(* Emitted into [run_z3_binary]'s prelude; None = z3/config default. *)
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

let serialize_expr (env : Dtencoding.z3_env) (query : Expr.expr) : string =
  let solver = mk_solver env.ctx None in
  Solver.add solver [ query ];
  Solver.to_string solver

let dump_queries entries =
  _log_dump_smt @@ fun _ ->
  List.iter
    (fun { Portfolio.label; query } ->
      let path =
        Filename.concat
          (Filename.get_temp_dir_name ())
          (Printf.sprintf "zutils_query_%i_%s.smt2" !query_counter label)
      in
      Out_channel.with_open_text path (fun oc -> output_string oc query);
      Printf.eprintf "Dumped SMT query to %s\n" path)
    entries

let run_z3_binary ~extra_bodies solver : smt_result * string option =
  let timeout =
    match !_timeout with Some t -> t | None -> get_prover_timeout_bound ()
  in
  (* [:timeout] is each child's only termination guarantee. *)
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
    (* [(get-info :reason-unknown)] is appended unconditionally; after sat/unsat z3
       answers `(:reason-unknown "")`. *)
    Printf.sprintf
      "%s%s(set-option :timeout %d)\n\
       %s%s\n\
       (check-sat)\n\
       (get-info :reason-unknown)\n"
      dt mq timeout rlimit_opt body
  in
  let axiom_body = Solver.to_string solver in
  let entries =
    [
      { Portfolio.label = "axiom"; query = wrap axiom_body };
      {
        Portfolio.label = "axiom_dt-eager";
        query = wrap ~dt_eager:true axiom_body;
      };
      {
        Portfolio.label = "axiom_mbqi-only";
        query = wrap ~mbqi_only:true axiom_body;
      };
    ]
    @ List.map
        (fun body -> { Portfolio.label = "functional"; query = wrap body })
        extra_bodies
  in
  dump_queries entries;
  Portfolio.solve entries

let select_axioms prop =
  let { ax_sys; _ } = get_prover () in
  Axiom.find_axioms ax_sys prop

let all_axioms () =
  let { ax_sys; _ } = get_prover () in
  Axiom.all_axioms ax_sys

let check_sat ~axioms ?(extra_bodies = []) prop =
  incr query_counter;
  let { env; _ } = get_prover () in
  let ctx = env.ctx in
  let z3_axioms = List.map (Propencoding.to_z3 env) axioms in
  let query = Propencoding.to_z3 env prop in
  let _ =
    _log_queries @@ fun _ ->
    Pp.printf "@{<bold>QUERY:@}\n%s\n" (Expr.to_string query)
  in
  let goal = mk_goal ctx true false false in
  Goal.add goal (z3_axioms @ [ query ]);
  let _ =
    _log_queries @@ fun _ ->
    Pp.printf "@{<bold>Goal:@}\n%s\n" (Goal.to_string goal)
  in
  let solver = mk_solver ctx None in
  Solver.add solver (get_formulas goal);
  let time_t, (res, won) =
    Sugar.clock (fun () -> run_z3_binary ~extra_bodies solver)
  in
  let () =
    _log_stat @@ fun _ ->
    Pp.printf "@{<bold>Z3 Solving time [q%i]: %.2f (%s, %i asserts, won:%s)@}\n"
      !query_counter time_t (layout_smt_result res)
      (1 + List.length z3_axioms)
      (match won with Some l -> l | None -> "-")
  in
  res

(* z3's [:reason-unknown] → which knob to raise to move the verdict. *)
let coercion_hint = function
  | Some r when String.starts_with ~prefix:"max. resource" r ->
      "raise rlimit if this verdict is decision-relevant"
  | Some ("timeout" | "canceled") ->
      "raise the prover timeout if this verdict is decision-relevant"
  | Some r -> Printf.sprintf "z3 reason-unknown: %s" r
  | None -> "raise rlimit if this verdict is decision-relevant"
