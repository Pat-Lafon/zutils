open Z3
open Solver
open Goal
open Sugar
open Syntax
open ZUtilsConfig
module Propencoding = Propencoding

type smt_result = SmtSat of Model.model | SmtUnsat | Timeout

let layout_model model =
  Sugar.short_str (ZUtilsConfig.get_max_printing_size ())
  @@ Z3.Model.to_string model

let layout_smt_result = function
  | SmtSat model ->
      ( ZUtilsLog.model @@ fun _ ->
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

let check_sat (task, prop) =
  let { goal; solver; ax_sys; ctx } = get_prover () in
  let axioms =
    List.map (Propencoding.to_z3 ctx) @@ Axiom.find_axioms ax_sys (task, prop)
  in
  let query = Propencoding.to_z3 ctx prop in
  let _ =
    ZUtilsLog.queries @@ fun _ ->
    Pp.printf "@{<bold>QUERY:@}\n%s\n" (Expr.to_string query)
  in
  Goal.reset goal;
  Goal.add goal (axioms @ [ query ]);
  let _ =
    ZUtilsLog.queries @@ fun _ ->
    Pp.printf "@{<bold>Goal:@}\n%s\n" (Goal.to_string goal)
  in
  (* let goal = Goal.simplify goal None in *)
  (* let _ = *)
  (*   ZUtilsLog.queries @@ fun _ -> *)
  (*   Pp.printf "@{<bold>Simplifid Goal:@}\n%s\n" (Goal.to_string goal) *)
  (* in *)
  Goal.add goal axioms;
  Solver.reset solver;
  Solver.add solver (get_formulas goal);
  let time_t, res = Sugar.clock (fun () -> handle_sat_result solver) in
  let () =
    ZUtilsLog.stat @@ fun _ ->
    Pp.printf "@{<bold>Z3 Solving time: %.2f@}\n" time_t
  in
  res

let check_sat_bool (task, prop) =
  let res = check_sat (task, prop) in
  let () =
    ZUtilsLog.queries @@ fun _ ->
    Pp.printf "@{<bold>SAT(%s): @} %s\n" (layout_smt_result res)
      (Front.layout_prop prop)
  in
  let res =
    match res with
    | SmtUnsat -> false
    | SmtSat model ->
        ( ZUtilsLog.model @@ fun _ ->
          Printf.printf "model:\n%s\n" (layout_model model) );
        true
    | Timeout ->
        (ZUtilsLog.queries @@ fun _ -> Pp.printf "@{<bold>SMTTIMEOUT@}\n");
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
let check_valid (task, prop) =
  let () = _store_input (task, prop) in
  (* let () = *)
  (*   Printf.printf "input:\n%s\n" *)
  (*     (Sexplib.Sexp.to_string @@ sexp_of_prop Nt.sexp_of_nt (Not prop)) *)
  (* in *)
  match check_sat (task, Not prop) with
  | SmtUnsat -> true
  | SmtSat model ->
      ( ZUtilsLog.model @@ fun _ ->
        Printf.printf "model:\n%s\n" (layout_model model) );
      false
  | Timeout ->
      (ZUtilsLog.queries @@ fun _ -> Pp.printf "@{<bold>SMTTIMEOUT@}\n");
      false
