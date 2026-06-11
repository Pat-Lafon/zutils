open Ast
open OcamlParser
open Parsetree
open Oparse
open Sugar
open Ast_helper

let get_str t =
  match t.ptyp_desc with
  | Ptyp_constr (name, []) -> List.nth (Longident.flatten name.txt) 0
  | _ -> _die [%here]

let rec core_type_to_t ct = core_type_desc_to_t ct.ptyp_desc

and object_to_labeled_type feild =
  match feild.pof_desc with
  | Otag (label, ct) -> label.txt#:(core_type_to_t ct)
  | _ -> _die_with [%here] "wrong record type"

and core_type_desc_to_t t =
  match t with
  | Ptyp_any -> _die_with [%here] "new we don't suport any type"
  | Ptyp_object (l, _) ->
      (* NOTE: In our type system, record type is anonymous type, thus use object type *)
      let fds = List.map object_to_labeled_type l in
      mk_record None fds
  | Ptyp_poly (lc :: ps, ct) ->
      Ty_poly (lc.txt, core_type_desc_to_t (Ptyp_poly (ps, ct)))
  | Ptyp_poly ([], ct) -> core_type_to_t ct
  | Ptyp_var name -> Ty_var name
  | Ptyp_arrow (_, t1, t2) -> Ty_arrow (core_type_to_t t1, core_type_to_t t2)
  | Ptyp_tuple ts -> Ty_tuple (List.map core_type_to_t ts)
  | Ptyp_constr (lc, ts) ->
      let c = String.concat "." @@ Longident.flatten lc.txt in
      Ty_constructor (c, List.map core_type_to_t ts)
  | Ptyp_class (_, _)
  | Ptyp_alias (_, _)
  | Ptyp_variant (_, _, _)
  | Ptyp_package _ | Ptyp_extension _ ->
      _die [%here]

let rec t_to_core_type t = Typ.mk (t_to_core_type_desc t)

and t_to_core_type_desc t =
  let open Longident in
  let open Location in
  let mk0 name = Ptyp_constr (mknoloc @@ Lident name, []) in
  (* let mk1 name t = Ptyp_constr (mknoloc @@ Lident name, [ t ]) in *)
  match t with
  | Ty_unknown -> mk0 "unknown"
  | Ty_var name ->
      let res = Ptyp_var name in
      (* let () = *)
      (*   Printf.printf "output res: %s\n" @@ string_of_core_type @@ desc_to_ct res *)
      (* in *)
      res
  | Ty_poly (p, nt) -> Ptyp_poly ([ mknoloc p ], t_to_core_type nt)
  | Ty_tuple t -> Ptyp_tuple (List.map t_to_core_type t)
  | Ty_arrow (t1, t2) ->
      Ptyp_arrow (Asttypes.Nolabel, t_to_core_type t1, t_to_core_type t2)
  | Ty_constructor (id, args) ->
      let id =
        match Longident.unflatten @@ String.split_on_char '.' id with
        | None -> _die [%here]
        | Some id -> id
      in
      Ptyp_constr (Location.mknoloc id, List.map t_to_core_type args)
  | Ty_record { fds; alias } ->
      let alias = match alias with None -> "_record" | Some alias -> alias in
      if Myconfig.get_show_record_type_fields () then
        let name_type = "record_name"#:(Ty_constructor (alias, [])) in
        Ptyp_object
          (List.map labeled_t_to_feild (name_type :: fds), Asttypes.Closed)
      else mk0 alias

and labeled_t_to_feild { x; ty = t } =
  Of.tag (Location.mknoloc x) (t_to_core_type t)

let core_type_to_notated_t ct =
  match ct.ptyp_desc with
  | Ptyp_extension (name, PTyp ty) -> (Some name.txt, core_type_to_t ty)
  | _ -> (None, core_type_to_t ct)

let notated_t_to_core_type (name, t) =
  let ct = t_to_core_type t in
  match name with
  | None -> ct
  | Some name -> desc_to_ct (Ptyp_extension (Location.mknoloc name, PTyp ct))

let layout_nt t = string_of_core_type (t_to_core_type t)

let nt_of_string str =
  core_type_to_t @@ Parse.core_type @@ Lexing.from_string str

let string_of_nts ts = Zdatatype.List.split_by_comma layout_nt ts

(* let%test "rev" = List.equal Int.equal (List.rev [ 3; 2; 1 ]) [ 1; 2 ] *)
(* let%test "parse1" = equal_nt int_ty (of_string "int") *)
(* let%test "parse2" = equal_nt bool_ty (of_string "bool") *)
(* let%test "parse3" = equal_nt (mk_arr bool_ty int_ty) (of_string "bool -> int") *)
(* let%test "parse4" = equal_nt (mk_arr bool_ty int_ty) (of_string "bool -> int") *)
(* let%test "parse5" = equal_nt (uninter_ty "path") (of_string "path") *)
(* let%test "parse6" = equal_nt (uninter_ty "Path.t") (of_string "Path.t") *)

(* let%test "parse7" = *)
(*   equal_nt *)
(*     (Ty_record [ ("z", Ty_bool); ("x", Ty_int) ]) *)
(*     (of_string "<x:int; z:bool>") *)
