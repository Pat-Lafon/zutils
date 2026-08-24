include Ast
include Subst

(* module SMTtyped = Typed.SMTtyped *)
(* module Notatedtyped = Typed.Notatedtyped *)
(* module Ntyped = Typed.Ntyped *)
(* module NOpttyped = Typed.NOpttyped *)
(* module Frontend = Frontend *)
(* module Connective = Connective *)
include Frontend
include Syntax
include Unification
open Sugar

let is_unkown = function Ty_unknown -> true | _ -> false
let known_opt = function Ty_unknown -> None | ty -> Some ty

let __force_known loc ty =
  if is_unkown ty then _die_with loc "unkonwn type" else ty

let __force_typed loc x = x#=>(__force_known loc)

(* let __type_unify = Unification.__type_unify layout_nt *)
(* let _type_unify = __type_unify *)
let mk_arr a b = Ty_arrow (a, b)
let layout = layout_nt
let layout_nt = layout_nt
let nt_of_string = nt_of_string
let string_of_nts = string_of_nts
let untyped x = { x; ty = Ty_unknown }
let nt_name nt = String.concat "_" @@ String.split_on_char ' ' @@ layout_nt nt

let instantiate_poly_type_var_in_smt =
  map_nt (function Ty_var _ -> int_ty | Ty_poly _ -> _die [%here] | ty -> ty)

let to_smtty t =
  let t =
    if Myconfig.get_instantiate_poly_type_var_in_smt () then
      instantiate_poly_type_var_in_smt t
    else t
  in
  let rec aux t =
    match t with
    | Ty_constructor ("bool", _) -> Smt_Bool
    | Ty_constructor ("int", _) -> Smt_Int
    | Ty_constructor ("nat", _) -> Smt_Int
    | Ty_constructor ("unit", _) -> Smt_Unit
    | Ty_constructor ("char", _) -> Smt_Char
    | Ty_constructor ("string", _) -> Smt_String
    | Ty_constructor ("float", _) -> Smt_Float64
    | Ty_constructor ("option", [ nt ]) -> Smt_option (aux nt)
    | Ty_constructor (name, []) -> Smt_Uninterp name
    | Ty_constructor (_, _) -> Smt_Uninterp (layout_nt t)
    | Ty_tuple l -> Smt_tuple (List.map aux l)
    | Ty_var _ -> Smt_Uninterp (layout_nt t)
    | Ty_record { fds; _ } ->
        Smt_record (List.map (fun x -> x#=>aux) (sort_record fds))
    | _ -> _die_with [%here] (spf "%s not a basic type" (show_nt t))
  in
  aux t

open Zdatatype

let rec layout_smtty = function
  | Smt_Bool -> "bool"
  | Smt_Int -> "int"
  | Smt_Unit -> "unit"
  | Smt_Char -> "char"
  | Smt_String -> "string"
  | Smt_Float64 -> "float"
  | Smt_Uninterp x -> x
  | Smt_option smtty -> spf "%s option" (layout_smtty smtty)
  | Smt_tuple ts -> spf "(%s)" (List.split_by " * " layout_smtty ts)
  | Smt_record ts ->
      spf "{%s}"
        (List.split_by "; " (fun x -> spf "%s: %s" x.x (layout_smtty x.ty)) ts)

let has_poly_tp = exists_nt (function Ty_poly _ -> true | _ -> false)

let lift_poly_tp tp =
  _assert [%here]
    (spf "not a well-formed poly type: %s" (Frontend.layout_nt tp))
    (wf_nt tp);
  let rec aux tp =
    match tp with
    | Ty_poly (p, nt) ->
        let ps, nt = aux nt in
        (p :: ps, nt)
    | _ -> ([], tp)
  in
  let ps, tp = aux tp in
  _assert [%here] "not a well-formed poly type" (not (has_poly_tp tp));
  _assert [%here] "same poly type var"
    (List.length ps == List.length (Zdatatype.List.slow_rm_dup String.equal ps));
  (ps, tp)
