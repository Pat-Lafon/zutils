open Language
open Normal_id_typing
open Normal_constant_typing
open Normal_qregex_typing
open Normal_regex_typing
open Sugar

type t = Nt.t

let rec bi_typed_inst_check (ctx : t ctx)
    (lit : (t option, t option inst) typed) (ty : t) : (t, t inst) typed =
  match (lit.x, ty) with
  | IVar _, _ | IConst _, _ ->
      let lit = bi_typed_inst_infer ctx lit.x in
      let _ = Nt._type_unify [%here] lit.ty ty in
      lit.x#:ty
  | IQregex q, _ -> (IQregex (bi_symbolic_qregex_check ctx q))#:Nt.Ty_unit
  | ILet { lhs; rhs; body }, _ ->
      let rhs = bi_typed_inst_infer ctx rhs in
      let lhs = lhs.x#:rhs.ty in
      let body = bi_typed_inst_check (add_to_right ctx lhs) body#:None ty in
      (ILet { lhs; rhs = rhs.x; body = body.x })#:body.ty
  | IApp _, _ ->
      let lit' = bi_typed_inst_infer ctx lit.x in
      let ty = Nt._type_unify [%here] lit'.ty ty in
      lit'.x#:ty
  | IAtomicF { args; regex }, _ ->
      let args = List.map (__force_typed [%here]) args in
      let regex = bi_symbolic_regex_check (add_to_rights ctx args) regex in
      let fty = Nt.construct_arr_tp (List.map _get_ty args, Nt.unit_ty) in
      (IAtomicF { args; regex })#:fty

and bi_typed_inst_infer (ctx : t ctx) (lit : t option inst) : (t, t inst) typed
    =
  match lit with
  | IVar id ->
      let id =
        match id.ty with
        | None -> bi_typed_id_infer ctx id
        | Some ty -> id.x#:ty
      in
      (* let () = Printf.printf "%s --> %s\n" id.x (Nt.layout id.ty) in *)
      (IVar id)#:id.ty
  | IConst c -> (IConst c)#:(infer_constant c)
  | IQregex q -> (IQregex (bi_symbolic_qregex_check ctx q))#:Nt.Ty_unit
  | IApp (mp, arg) ->
      let mp = bi_typed_inst_infer ctx mp in
      let arg = bi_typed_inst_infer ctx arg in
      (* let () = *)
      (*   Printf.printf "%s -- %s\n" *)
      (*     (layout_inst Nt.layout mp.x) *)
      (*     (layout_inst Nt.layout arg.x) *)
      (* in *)
      let mp_ty = Nt._type_unify [%here] mp.ty (Nt.mk_arr arg.ty Ty_unknown) in
      let mp = mp.x#:mp_ty in
      let retty =
        match mp_ty with Nt.Ty_arrow (_, t) -> t | _ -> _die [%here]
      in
      (IApp (mp.x, arg.x))#:retty
  | ILet { lhs; rhs; body } ->
      let rhs = bi_typed_inst_infer ctx rhs in
      let lhs = lhs.x#:rhs.ty in
      let body = bi_typed_inst_infer (add_to_right ctx lhs) body in
      (ILet { lhs; rhs = rhs.x; body = body.x })#:body.ty
  | IAtomicF { args; regex } ->
      let args = List.map (__force_typed [%here]) args in
      let regex = bi_symbolic_regex_check (add_to_rights ctx args) regex in
      let fty = Nt.construct_arr_tp (List.map _get_ty args, Nt.unit_ty) in
      (IAtomicF { args; regex })#:fty
