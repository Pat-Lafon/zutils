open Z3
open Z3aux
open Syntax
open Sugar

let to_z3 ctx prop =
  let rec aux prop =
    match prop with
    | Implies (p1, p2) ->
        let () =
          ZUtilsLog.z3encode @@ fun () ->
          Pp.printf "implies %s %s\n" (Front.layout p1) (Front.layout p2)
        in
        let e1 = aux p1 in
        let e2 = aux p2 in
        let () =
          ZUtilsLog.z3encode @@ fun () ->
          Pp.printf "implies %s %s\n" (Expr.to_string e1) (Expr.to_string e2)
        in
        Boolean.mk_implies ctx e1 e2
    | Ite (p1, p2, p3) -> Boolean.mk_ite ctx (aux p1) (aux p2) (aux p3)
    | Not p -> Boolean.mk_not ctx (aux p)
    | And ps -> Boolean.mk_and ctx (List.map aux ps)
    | Or ps -> Boolean.mk_or ctx (List.map aux ps)
    | Iff (p1, p2) -> Boolean.mk_iff ctx (aux p1) (aux p2)
    | Forall { qv; body } ->
        make_forall ctx [ tpedvar_to_z3 ctx (qv.ty, qv.x) ] (aux body)
    | Exists { qv; body } ->
        make_exists ctx [ tpedvar_to_z3 ctx (qv.ty, qv.x) ] (aux body)
    | Lit lit -> Litencoding.typed_lit_to_z3 ctx lit
  in
  let p1 = to_nnf prop in
  let () =
    ZUtilsLog.queries @@ fun _ ->
    Pp.printf "@{<bold>To NNF:@} %s\n" (Front.layout_prop p1)
  in
  aux p1

(* Z3 binds each quantifier by abstracting its constant out of the body, so a
   binder name reused by a sibling or an inner quantifier needs no renaming. *)
let%test_module "repeated binder names" =
  (module struct
    let () = ZUtilsConfig.(set (Result.get_ok (of_yojson (`Assoc []))))
    let ctx = Z3.mk_context []
    let u = "u"#:Nt.int_ty
    let eq i = lit_to_prop (mk_int_l1_eq_l2 (AVar u) (AC (I i)))

    let check p =
      let s = Z3.Solver.mk_solver ctx None in
      Z3.Solver.add s [ to_z3 ctx p ];
      Z3.Solver.check s []

    let%test "siblings" =
      check
        (And [ Exists { qv = u; body = eq 1 }; Exists { qv = u; body = eq 2 } ])
      = Z3.Solver.SATISFIABLE

    let%test "an inner binder shadows an outer one" =
      check
        (Exists { qv = u; body = And [ eq 1; Exists { qv = u; body = eq 2 } ] })
      = Z3.Solver.SATISFIABLE

    let%test "a shadowing exists under a forall" =
      check (Not (Forall { qv = u; body = Exists { qv = u; body = eq 2 } }))
      = Z3.Solver.UNSATISFIABLE
  end)
