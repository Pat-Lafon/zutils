open Ast
open Sugar

let _lift_poly_tp tp =
  let rec aux tp =
    match tp with
    | Ty_poly (p, nt) ->
        let ps, nt = aux nt in
        (p :: ps, nt)
    | _ -> ([], tp)
  in
  let ps, tp = aux tp in
  (ps, tp)

let gather_type_vars t =
  let open Zdatatype in
  let rec aux m = function
    | Ty_var x -> StrMap.add x () m
    | Ty_unknown -> m
    | Ty_constructor (_, tps) -> List.fold_left aux m tps
    | Ty_record { fds; _ } -> List.fold_left (fun m x -> aux m x.ty) m fds
    | Ty_arrow (nt1, nt2) -> List.fold_left aux m [ nt1; nt2 ]
    | Ty_tuple nts -> List.fold_left aux m nts
    | Ty_poly (x, t) -> StrMap.remove x (aux m t)
  in
  StrMap.to_key_list @@ aux StrMap.empty t

let rec construct_poly_nt = function
  | [], ty -> ty
  | x :: xs, ty -> Ty_poly (x, construct_poly_nt (xs, ty))

let wf_nt t =
  let rec aux tvars = function
    | Ty_var _ | Ty_unknown -> true
    | Ty_constructor (_, tps) -> List.for_all (aux tvars) tps
    | Ty_record { fds; _ } -> List.for_all (fun x -> aux tvars x.ty) fds
    | Ty_arrow (nt1, nt2) -> List.for_all (aux tvars) [ nt1; nt2 ]
    | Ty_tuple nts -> List.for_all (aux tvars) nts
    | Ty_poly _ -> false
  in
  let rec aux_top tvars = function
    | Ty_poly (x, ty) -> aux_top (x :: tvars) ty
    | _ as ty -> aux tvars ty
  in
  aux_top [] t

let close_poly_nt loc t =
  let t = construct_poly_nt (gather_type_vars t, t) in
  _assert loc
    (spf "not a well-formed poly type: %s" (Frontend.layout_nt t))
    (wf_nt t);
  t

let destruct_arr_tp tp =
  let rec aux = function
    | Ty_arrow (t1, t2) ->
        let argsty, bodyty = aux t2 in
        (t1 :: argsty, bodyty)
    | ty -> ([], ty)
  in
  aux tp

let rec construct_arr_tp = function
  | [], retty -> retty
  | h :: t, retty -> Ty_arrow (h, construct_arr_tp (t, retty))

(* let core_type_to_t ct = close_poly_nt [%here] (Frontend.core_type_to_t ct) *)
let of_core_type = Frontend.core_type_to_t
let to_core_type = Frontend.t_to_core_type
let layout_nt = Frontend.layout_nt

(** Record type *)

(* NOTE: the Z3 encoding use list instead of map, thus we need to make sure the input list has the same order *)

let sort_record args =
  if Myconfig.get_if_sort_record () then
    List.sort (fun a b -> String.compare a.x b.x) args
  else args

let as_record loc = function
  | Ty_record { fds; _ } -> sort_record fds
  | _ -> _die loc

let as_const_ty_opt = function Ty_constructor (x, []) -> Some x | _ -> None

let get_feild loc t name =
  let args = as_record loc t in
  match List.find_opt (fun y -> String.equal name y.x) args with
  | None ->
      Printf.printf "Cannot find feild: %s\n" name;
      _die [%here]
  | Some n -> n.ty

let get_feild_idx loc t name =
  let args = as_record loc t in
  match List.find_index (fun y -> String.equal name y.x) args with
  | None -> _die [%here]
  | Some n -> n

let mk_uninterp name = Ty_constructor (name, [])
let mk_type_var name = Ty_var name

let mk_tuple loc l =
  match l with [] -> _die loc | [ x ] -> x | xs -> Ty_tuple xs

(** equal type *)

let erase_record_alias =
  let rec aux ty =
    match ty with
    | Ty_var _ | Ty_unknown -> ty
    | Ty_constructor (op, tps) -> Ty_constructor (op, List.map aux tps)
    | Ty_record { fds; _ } ->
        let fds = List.map (fun x -> x#=>aux) fds in
        Ty_record { fds; alias = None }
    | Ty_arrow (nt1, nt2) -> Ty_arrow (aux nt1, aux nt2)
    | Ty_tuple nts -> Ty_tuple (List.map aux nts)
    | Ty_poly (x, t) -> Ty_poly (x, aux t)
  in
  aux

let raw_equal_nt = equal_nt

let equal_nt nt1 nt2 =
  raw_equal_nt (erase_record_alias nt1) (erase_record_alias nt2)
