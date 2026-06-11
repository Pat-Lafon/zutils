open Z3
open Solver
open Goal
open Sugar
open Syntax
open Myconfig
module Propencoding = Propencoding

type smt_result = SmtSat of Model.model | SmtUnsat | Timeout

let layout_model model =
  Sugar.short_str (Myconfig.get_max_printing_size ())
  @@ Z3.Model.to_string model

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

let reset_solver_in_prover () =
  match !_prover with
  | Some p ->
      let solver = mk_solver p.ctx None in
      let p = { p with solver } in
      let () = _prover := Some p in
      p
  | None ->
      let p = mk_prover () in
      let () = _prover := Some p in
      p

let get_prover () =
  match !_prover with
  | Some p -> p
  | None ->
      let p = mk_prover () in
      let () = _prover := Some p in
      p

let get_ctx () = (get_prover ()).ctx

let query_counter = ref 0

let set_z3_rlimit rlimit =
  Z3.Params.update_param_value (get_ctx ()) "rlimit" (string_of_int rlimit)

let set_z3_timeout (timeout : int option) =
  match timeout with
  | None -> ()
  | Some t ->
      Z3.Params.update_param_value (get_ctx ()) "timeout" (string_of_int t)

let update_axioms axioms =
  let ctx = get_ctx () in
  let axioms =
    List.map
      (fun (name, tasks, prop) ->
        let z3_prop = Propencoding.to_z3 ctx prop in
        (name, tasks, prop, z3_prop))
      axioms
  in
  match !_prover with
  | Some p ->
      _prover := Some { p with ax_sys = Axiom.add_laxioms p.ax_sys axioms }
  | None ->
      let p = mk_prover () in
      _prover := Some { p with ax_sys = Axiom.add_laxioms p.ax_sys axioms }

let handle_sat_result solver =
  (* let _ = printf "solver_result\n" in *)
  match check solver [] with
  | UNSATISFIABLE -> SmtUnsat
  | UNKNOWN ->
      (* raise (InterExn "time out!") *)
      (* Printf.printf "\ttimeout\n"; *)
      Timeout
  | SATISFIABLE -> (
      match Solver.get_model solver with
      | None -> failwith "never happen"
      | Some m -> SmtSat m)

let select_axioms (task, prop) =
  let { ax_sys; _ } = get_prover () in
  Axiom.find_axioms ax_sys (task, prop)

let check_sat ~axioms (_task, prop) =
  incr query_counter;
  let { goal; solver; ctx; _ } = get_prover () in
  let z3_axioms = List.map (Propencoding.to_z3 ctx) axioms in
  let query = Propencoding.to_z3 ctx prop in
  let _ =
    _log_queries @@ fun _ ->
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
  (match Sys.getenv_opt "TOTEM_DUMP_SMT" with
   | None -> ()
   | Some _ ->
       let idx = !query_counter in
       let path =
         Filename.concat (Filename.get_temp_dir_name ())
           (Printf.sprintf "cobb_query_%i.smt2" idx)
       in
       let oc = open_out path in
       output_string oc (Solver.to_string solver);
       output_string oc "\n(check-sat)\n";
       close_out oc;
       Printf.eprintf "Dumped SMT query to %s\n" path);
  let time_t, res = Sugar.clock (fun () -> handle_sat_result solver) in
  let () =
    _log_stat @@ fun _ -> Pp.printf "@{<bold>Z3 Solving time: %.2f@}\n" time_t
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

let _tmp_path_prefix str = spf "/tmp/%s.scm" str

let _store_input (task, prop) =
  let path =
    match task with
    | None -> _tmp_path_prefix "tmp"
    | Some str -> _tmp_path_prefix str
  in
  Sexplib.Sexp.save path (sexp_of_prop Nt.sexp_of_nt (Not prop))

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
