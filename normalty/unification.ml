open Sugar
open Ast
open Zdatatype
open Subst
open Syntax

module BoundConstraints = struct
  type bc = { type_vars : unit StrMap.t; cs : (t * t) list }

  let exists vars p = StrMap.exists (fun y () -> String.equal p y) vars

  let uniquelize (vars, t) =
    let ps, t = _lift_poly_tp t in
    let rec aux vars (ps, t) =
      match ps with
      | [] -> (vars, t)
      | p :: ps ->
          if exists vars p then (
            let p' = Rename.unique p in
            let p' = if exists vars p' then Rename.unique p' else p' in
            _assert [%here]
              (spf "rename success: %s in [%s]" p'
                 (StrList.to_string (StrMap.to_key_list vars)))
              (not (exists vars p'));
            aux (StrMap.add p' () vars) (ps, subst_nt (p, Ty_var p') t))
          else aux (StrMap.add p () vars) (ps, t)
    in
    let res = aux vars (ps, t) in
    let () =
      ZUtilsLog.unification (fun () ->
          Pp.printf "@{<bold>uniquelize@}: %s :: %s ====>>===== %s :: %s\n"
            (StrList.to_string (StrMap.to_key_list vars))
            (layout_nt t)
            (StrList.to_string (StrMap.to_key_list (fst res)))
            (layout_nt (snd res)))
    in
    res

  let add_type { type_vars; cs } t =
    let type_vars, t = uniquelize (type_vars, t) in
    ({ type_vars; cs }, t)

  let add_type_var { type_vars; cs } pt =
    if StrMap.mem pt type_vars then
      _die_with [%here] (spf "same poly var: %s" pt)
    else { type_vars = StrMap.add pt () type_vars; cs }

  let add bc (t1, t2) =
    let type_vars, t1 = uniquelize (bc.type_vars, t1) in
    let type_vars, t2 = uniquelize (type_vars, t2) in
    _assert [%here] "new poly type var"
      (StrMap.cardinal bc.type_vars == StrMap.cardinal type_vars);
    ({ bc with cs = (t1, t2) :: bc.cs }, (t1, t2))

  let fresh { type_vars; cs } =
    let x = Rename.fresh_type_var () in
    (* let () = Printf.printf "fresh: %s\n" x in *)
    _assert [%here] "fresh var create success" (not (exists type_vars x));
    ({ type_vars = StrMap.add x () type_vars; cs }, Ty_var x)

  let empty vars =
    {
      type_vars = StrMap.from_kv_list (List.map (fun x -> (x, ())) vars);
      cs = [];
    }

  let layout bc =
    spf "type vars: %s;\n constraints: %s;\n"
      (StrList.to_string (StrMap.to_key_list bc.type_vars))
      (List.split_by ", "
         (fun (a, b) -> spf "%s = %s" (layout_nt a) (layout_nt b))
         bc.cs)
end

(* let add_cs (x, y) cs = if equal_nt x y then cs else (x, y) :: cs *)

let type_unification m (cs : (t * t) list) =
  let rec aux m cs =
    let () =
      ZUtilsLog.unification (fun () ->
          Pp.printf "@{<bold>m@}: %s\n"
            (List.split_by_comma
               (fun (x, ty) -> spf "%s := %s" x (layout_nt ty))
               (StrMap.to_kv_list m));
          Pp.printf "@{<bold>cs@}: %s\n"
            (List.split_by_comma
               (fun (x, ty) -> spf "%s = %s" (layout_nt x) (layout_nt ty))
               cs))
    in
    match cs with
    | [] -> Some m
    | (t1, t2) :: cs -> (
        let err () =
          let () =
            ZUtilsLog.unification @@ fun _ ->
            Printf.printf "cannot solve %s = %s\n" (layout_nt t1) (layout_nt t2)
          in
          None
        in
        match (t1, t2) with
        | Ty_unknown, _ | _, Ty_unknown -> aux m cs
        | Ty_var n, Ty_var k ->
            if String.compare n k == 0 then aux m cs
            else if String.compare n k > 0 then
              let m = subst_on_sol (n, t2) m in
              let cs = subst_on_cs (n, t2) cs in
              aux (StrMap.add n t2 m) cs
            else aux m ((Ty_var k, Ty_var n) :: cs)
        | Ty_var n, _ ->
            if List.exists (String.equal n) @@ gather_type_vars t2 then err ()
            else
              let m = subst_on_sol (n, t2) m in
              let cs = subst_on_cs (n, t2) cs in
              aux (StrMap.add n t2 m) cs
        | _, Ty_var n ->
            if List.exists (String.equal n) @@ gather_type_vars t1 then err ()
            else
              let m = subst_on_sol (n, t1) m in
              let cs = subst_on_cs (n, t1) cs in
              aux (StrMap.add n t1 m) cs
        | Ty_constructor (id1, ts1), Ty_constructor (id2, ts2) ->
            if String.equal id1 id2 && List.length ts1 == List.length ts2 then
              aux m (List.combine ts1 ts2 @ cs)
            else err ()
        | Ty_arrow (t11, t12), Ty_arrow (t21, t22) ->
            aux m ((t11, t21) :: (t12, t22) :: cs)
        (* unfold singleton tuple *)
        | Ty_tuple [ t1 ], _ -> aux m ((t1, t2) :: cs)
        | _, Ty_tuple [ t2 ] -> aux m ((t1, t2) :: cs)
        | Ty_tuple ts1, Ty_tuple ts2 when List.length ts1 == List.length ts2 ->
            aux m (List.combine ts1 ts2 @ cs)
        | Ty_record { fds = l1; _ }, Ty_record { fds = l2; _ } ->
            let tab = Hashtbl.create (List.length l1) in
            let () = List.iter (fun x -> Hashtbl.add tab x.x x.ty) l1 in
            let cs =
              List.fold_left
                (fun res x ->
                  match Hashtbl.find_opt tab x.x with
                  | None -> _die_with [%here] (spf "cannot find field %s" x.x)
                  | Some t' -> (t', x.ty) :: res)
                cs l2
            in
            aux m cs
        | _, _ -> if equal_nt t1 t2 then aux m cs else err ())
  in
  aux m cs

let unify_two_types_opt (poly_vars : string list) (t1, t2) =
  let bc, (t1, _) = BoundConstraints.(add (empty poly_vars) (t1, t2)) in
  let solution = type_unification StrMap.empty bc.cs in
  match solution with None -> None | Some sol -> Some (msubst_nt sol t1)

let unify_two_types loc (poly_vars : string list) (t1, t2) =
  match unify_two_types_opt poly_vars (t1, t2) with
  | None -> _die_with loc __FUNCTION__
  | Some t -> t
