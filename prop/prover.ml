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

let%test "a type-variable sort survives serialization" =
  ZUtilsConfig.(set (Result.get_ok (of_yojson (`Assoc []))));
  let ctx = mk_context [] in
  let x = Expr.mk_const_s ctx "x" (Z3aux.tp_to_sort ctx (Nt.Ty_var "a1")) in
  let text = serialize ctx [ Boolean.mk_eq ctx x x ] in
  match SMT.parse_smtlib2_string ctx text [] [] [] [] with
  | _ -> true
  | exception Z3.Error _ -> false

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
let portfolio_entries ~functional_bodies axiom_body : Portfolio.entry list =
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
  @ List.mapi
      (fun i body ->
        {
          Portfolio.label = Printf.sprintf "functional_%i" i;
          query = wrap body;
        })
      functional_bodies

(* Every registered axiom, encoded and printed as [check_sat] sends them *)
let serialize_all_axioms () =
  let { ctx; ax_sys } = get_prover () in
  serialize ctx
    (List.map
       (fun (_, p) -> Propencoding.to_z3 ctx p)
       (Axiom.all_axioms ax_sys))

let report_unclosed loc query =
  let fvs = fv_prop query in
  _assert loc
    (spf "the query has free variables %s"
       (List.split_by_comma
          (function { x; ty } -> spf "%s:%s" x (Nt.layout ty))
          fvs))
    (0 = List.length fvs)

let check_sat ?(functional_bodies = fun _ -> []) loc prop =
  incr query_counter;
  let () = report_unclosed loc prop in
  let { ctx; ax_sys } = get_prover () in
  let z3_axioms =
    List.map (fun (_, p) -> Propencoding.to_z3 ctx p)
    @@ Axiom.find_axioms ax_sys prop
  in
  let query = Propencoding.to_z3 ctx prop in
  let _ =
    ZUtilsLog.queries @@ fun _ ->
    Pp.printf "@{<bold>QUERY:@}\n%s\n" (Expr.to_string query)
  in
  let body = serialize ctx (z3_axioms @ [ query ]) in
  let entries =
    portfolio_entries ~functional_bodies:(functional_bodies prop) body
  in
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
  | Some r
    when r = "canceled" || r = "push canceled"
         || String.starts_with ~prefix:"max. resource" r ->
      "raise rlimit first, then debug the query"
  | Some "timeout" ->
      "raise the prover timeout first, then debug the query"
  | Some r -> Printf.sprintf "z3 reason-unknown: %s" r
  | None -> "z3 gave no reason-unknown"

(* How [check_valid_bool] / [check_sat_bool] answer when Z3 returns unknown. *)
type on_unknown = Accept | Reject | Raise

let coerce ~reason ~desc on_unknown =
  match on_unknown with
  | Raise ->
      failwith
        (Printf.sprintf "non-decisive Z3 verdict at q%i; %s" !query_counter
           (coercion_hint reason))
  | Accept | Reject ->
      let b = on_unknown = Accept in
      ( ZUtilsLog.queries @@ fun () ->
        Printf.eprintf
          "[non-decisive Z3 verdict] q%i: timeout/unknown coerced to %s; %s.\n"
          !query_counter (desc b) (coercion_hint reason) );
      b

let check_valid ?functional_bodies loc query =
  match check_sat ?functional_bodies loc (smart_not query) with
  | SmtUnsat -> SmtValid
  | SmtSat -> SmtInvalid
  | Unknown reason -> Unknown reason

let check_sat_bool ?functional_bodies loc query ~on_unknown =
  match check_sat ?functional_bodies loc query with
  | SmtSat -> true
  | SmtUnsat -> false
  | Unknown reason ->
      coerce ~reason
        ~desc:(fun b -> if b then "inhabited" else "uninhabited")
        on_unknown

let check_valid_bool ?functional_bodies loc query ~on_unknown =
  match check_valid ?functional_bodies loc query with
  | SmtValid -> true
  | SmtInvalid -> false
  | Unknown reason ->
      coerce ~reason
        ~desc:(fun b -> if b then "valid" else "invalid")
        on_unknown
