open Z3
open Z3aux
open Syntax
open Sugar
open Zdatatype

let unique_quantifiers prop =
  let rec aux prop =
    match prop with
    | Exists { body; qv } | Forall { body; qv } ->
        let* m = aux body in
        if StrSet.mem qv.x m then (
          Printf.printf "prop %s\n" (Front.layout_prop prop);
          Printf.printf "duplicate quantifier %s\n" qv.x;
          None)
        else Some (StrSet.add qv.x m)
    | And l | Or l -> aux_multi l
    | Implies (e1, e2) -> aux_multi [ e1; e2 ]
    | Lit _ -> Some StrSet.empty
    | Iff (e1, e2) -> aux_multi [ e1; e2 ]
    | Ite (e1, e2, e3) -> aux_multi [ e1; e2; e3 ]
    | Not e -> aux e
  and aux_multi l =
    List.fold_left
      (fun m m' ->
        let* m = m in
        let* m' = m' in
        let res = StrSet.union m m' in
        if StrSet.cardinal res != StrSet.cardinal m + StrSet.cardinal m' then (
          (let layout m = StrList.to_string @@ StrSet.to_list m in
           Printf.printf "[%s] ?= [%s] + [%s]\n" (layout res) (layout m)
             (layout m'));
          None)
        else Some res)
      (Some StrSet.empty) (List.map aux l)
  in
  match aux prop with None -> false | Some _ -> true

let to_z3 (env : Dtencoding.z3_env) prop =
  let ctx = env.ctx in
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
        make_forall ctx [ tpedvar_to_z3 env (qv.ty, qv.x) ] (aux body)
    | Exists { qv; body } ->
        make_exists ctx [ tpedvar_to_z3 env (qv.ty, qv.x) ] (aux body)
    | Lit lit -> Litencoding.typed_lit_to_z3 env lit
  in
  let () =
    ZUtilsLog.debug @@ fun () ->
    _assert [%here] "sanity check" (unique_quantifiers prop)
  in
  let p1 = to_nnf prop in
  let () =
    ZUtilsLog.queries @@ fun _ ->
    Pp.printf "@{<bold>To NNF:@} %s\n" (Front.layout_prop p1)
  in
  aux p1
