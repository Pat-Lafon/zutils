open Sugar
open Ast

let subst_nt (id, t') t =
  let rec aux t =
    match t with
    | Ty_unknown -> t
    | Ty_var x -> if streq x id then t' else t
    | Ty_poly (y, nt) ->
        if String.equal id y then Ty_poly (y, nt) else Ty_poly (y, aux nt)
    | Ty_arrow (t1, t2) -> Ty_arrow (aux t1, aux t2)
    | Ty_tuple xs -> Ty_tuple (List.map aux xs)
    | Ty_constructor (id, args) -> Ty_constructor (id, List.map aux args)
    | Ty_record { alias; fds } ->
        Ty_record { alias; fds = List.map (fun x -> x#=>aux) fds }
  in
  aux t

let subst_uninterpreted_type (id, t') t =
  let rec aux t =
    match t with
    | Ty_unknown | Ty_var _ -> t
    | Ty_poly (y, nt) ->
        if String.equal id y then Ty_poly (y, nt) else Ty_poly (y, aux nt)
    | Ty_arrow (t1, t2) -> Ty_arrow (aux t1, aux t2)
    | Ty_tuple xs -> Ty_tuple (List.map aux xs)
    | Ty_constructor (op, []) when String.equal op id -> t'
    | Ty_constructor (op, args) -> Ty_constructor (op, List.map aux args)
    | Ty_record { alias; fds } ->
        Ty_record { alias; fds = List.map (fun x -> x#=>aux) fds }
  in
  aux t

let subst_constructor_nt (name, f) =
  map_nt (function
    | Ty_constructor (id, args) when String.equal id name -> f args
    | ty -> ty)

let subst_alias_in_record_nt (fdnames, new_alias) =
  map_nt (function
    | Ty_record { alias; fds } ->
        let fds = Syntax.sort_record fds in
        let alias =
          if List.equal String.equal (List.map _get_x fds) fdnames then
            new_alias
          else alias
        in
        Ty_record { alias; fds }
    | ty -> ty)

open Zdatatype

let msubst_nt (m : t StrMap.t) = StrMap.fold (fun x ty -> subst_nt (x, ty)) m
let subst_on_sol (i, t) m = StrMap.map (subst_nt (i, t)) m
let subst_on_cs (i, t) cs = List.map (map2 (subst_nt (i, t))) cs
