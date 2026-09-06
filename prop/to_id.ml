open OcamlParser
open Oparse
open Parsetree
open Sugar
open Ast_helper
open Common
(* open Syntax.NTyped *)

let opt_typed_id_to_pattern id =
  let pat = Pat.var (Location.mknoloc id.x) in
  match id.ty with
  | None -> pat
  | Some ty -> Pat.constraint_ pat (Nt.t_to_core_type ty)

let opt_typed_ids_to_pattern ids =
  Pat.tuple (List.map opt_typed_id_to_pattern ids)

let longid_to_id c = String.concat "." @@ Longident.flatten c.Location.txt

let id_to_longid x =
  let strs = String.split_on_char '.' x in
  match Longident.unflatten strs with
  | Some x -> Location.mknoloc x
  | None -> _die [%here]

let id_of_pattern pattern =
  match pattern.ppat_desc with
  | Ppat_var ident -> ident.txt
  | Ppat_any -> "_"
  | Ppat_construct (name, None) -> longid_to_id name
  | _ -> _die [%here]

let rec typed_id_of_pattern pattern =
  match pattern.ppat_desc with
  | Ppat_var ident -> Nt.untyped ident.txt
  | Ppat_any -> Nt.untyped "_"
  | Ppat_constraint (pat, ct) ->
      let x = typed_id_of_pattern pat in
      x.x#:(Nt.core_type_to_t ct)
  | Ppat_construct (name, None) -> Nt.untyped @@ longid_to_id name
  | _ -> _die [%here]

let id_of_expr expr =
  match expr.pexp_desc with
  | Pexp_ident id -> longid_to_id id
  | _ ->
      Printf.printf "%s\n" (string_of_expression expr);
      _die [%here]

let id_of_expr_opt expr =
  match expr.pexp_desc with
  | Pexp_ident id -> Some (longid_to_id id)
  | _ -> None

let rec typed_id_of_expr expr =
  match expr.pexp_desc with
  | Pexp_constraint (expr, ty) ->
      (typed_id_of_expr expr).x#:(Nt.core_type_to_t ty)
  | Pexp_ident id -> Nt.untyped (longid_to_id id)
  | _ ->
      Printf.printf "%s\n" (string_of_expression expr);
      _die [%here]
