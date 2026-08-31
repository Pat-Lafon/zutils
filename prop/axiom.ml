(** Axiom system *)

open Syntax
open Zdatatype
open Sugar

let add_laxiom asys (name, tasks, prop, z3_prop) =
  let tasks = StrSet.of_list tasks in
  let preds = StrSet.of_list @@ get_fv_preds_from_prop prop in
  if StrMap.mem name asys then _die [%here]
  else StrMap.add name { tasks; preds; prop; z3_prop } asys

let add_laxioms asys l = List.fold_left add_laxiom asys l

let find_axioms_by_task asys task =
  let m = StrMap.filter (fun _ { tasks; _ } -> StrSet.mem task tasks) asys in
  StrMap.to_key_list m

let find_axioms_by_preds asys query_preds =
  let m =
    StrMap.filter
      (fun name { preds; _ } ->
        ( ZUtilsLog.axiom @@ fun () ->
          Pp.printf "@{<bold>in %s@}: %s\n" name
            (StrList.to_string @@ StrSet.to_list preds) );
        StrSet.subset preds query_preds)
      asys
  in
  StrMap.to_key_list m

let rules = [ (StrSet.of_list [ "hd" ], [ "list_mem" ]) ]

let pred_extension (_, ps) =
  let ps =
    List.fold_left
      (fun ps (rname, new_preds) ->
        let new_preds = if StrSet.subset rname ps then new_preds else [] in
        let ps = StrSet.add_seq (List.to_seq new_preds) ps in
        ps)
      ps rules
  in
  ps

(** instantiate_poly_axioms *)

(* The first type has poly var *)
let find_first_poly_type_from_axiom prop =
  let rec aux prop =
    match prop with
    | Exists { body; qv } | Forall { body; qv } -> (
        (* let () = Printf.printf "qv.ty : %s\n" (Nt.layout qv.ty) in *)
        match Nt.gather_type_vars qv.ty with
        | [ x ] when String.equal unified_axiom_type_var x -> Some qv
        | [] -> aux body
        | _ -> _die [%here])
    | And l | Or l -> aux_multi l
    | Implies (e1, e2) -> aux_multi [ e1; e2 ]
    | Lit _ -> None
    | Iff (e1, e2) -> aux_multi [ e1; e2 ]
    | Ite (e1, e2, e3) -> aux_multi [ e1; e2; e3 ]
    | Not e -> aux e
  and aux_multi l =
    List.fold_left
      (fun res x -> match res with None -> aux x | Some qv -> Some qv)
      None l
  in
  match aux prop with
  | None ->
      let () =
        ZUtilsLog.axiom @@ fun () ->
        Printf.printf "normal type %s\n" (Front.layout_prop prop)
      in
      None
  | Some x ->
      let () =
        ZUtilsLog.axiom @@ fun () ->
        Pp.printf "@{<bold>Axiom Indicator Type %s@} in %s\n" (Nt.layout x.ty)
          (Front.layout_prop prop)
      in
      Some x.ty

type inst_res = Mono | NoPoly | PolyAss of Nt.t

let gather_indicator_types query axioms =
  let typed_preds = get_tfv_preds_from_prop query in
  let preds_in_aximos =
    List.fold_left
      (fun s (_, { preds; _ }) -> StrSet.union preds s)
      StrSet.empty axioms
  in
  let typed_preds =
    List.filter (fun x -> StrSet.mem x.x preds_in_aximos) typed_preds
  in
  let get_actual_types pred_name =
    List.filter_map
      (fun p ->
        if String.equal pred_name p.x then
          let params, _ = Nt.destruct_arr_tp p.ty in
          match params with
          | [] ->
              None
              (* _die_with [%here] (spf "%s: %s" pred_name (Nt.layout p.ty)) *)
          | x :: _ -> Some x
        else None)
      typed_preds
  in
  let indicator_types =
    List.slow_rm_dup Nt.equal_nt
    @@ List.concat_map
         (fun pred_name -> get_actual_types pred_name.x)
         typed_preds
  in
  let instantiate_axiom_by_ty ax ax_fst_ty ty =
    let tvars = Nt.gather_type_vars ty in
    let ty =
      List.fold_right (fun id -> Nt.subst_nt (id, Nt.mk_uninterp id)) tvars ty
    in
    let () =
      ZUtilsLog.axiom @@ fun () ->
      Pp.printf "prop: %s\nunify %s and %s\n"
        (Front.layout_prop ax.prop)
        (Nt.layout ax_fst_ty) (Nt.layout ty)
    in
    let* m = Nt.type_unification StrMap.empty [ (ax_fst_ty, ty) ] in
    let solution_ty =
      match StrMap.find_opt m unified_axiom_type_var with
      | None ->
          let () =
            Pp.printf "%s\n"
              (List.split_by ";" (fun (x, ty) ->
                   spf "%s := %s" x (Nt.layout ty))
              @@ StrMap.to_kv_list m)
          in
          _die [%here]
      | Some ty ->
          let ty =
            List.fold_right
              (fun id -> Nt.subst_uninterpreted_type (id, Nt.mk_type_var id))
              tvars ty
          in
          ty
    in
    Some
      ( solution_ty,
        map_prop (Nt.subst_nt (unified_axiom_type_var, solution_ty)) ax.prop )
  in
  let instantiate_axiom (name, ax) =
    match find_first_poly_type_from_axiom ax.prop with
    | None -> [ ((name, None), ax.prop) ]
    | Some ax_fst_ty -> (
        let l =
          List.filter_map (instantiate_axiom_by_ty ax ax_fst_ty) indicator_types
        in
        match l with
        | [] ->
            ( ZUtilsLog.axiom @@ fun () ->
              Printf.printf
                "Warning: axiom [%s] should at least have one instantiation."
                name );
            []
        | _ -> List.map (fun (ty, prop) -> ((name, Some ty), prop)) l)
  in
  let props = List.concat_map instantiate_axiom axioms in
  let () =
    ZUtilsLog.axiom @@ fun () ->
    List.iter
      (fun ((name, ty), _) ->
        Pp.printf "%s::@{<bold>%s@}\n" name
          (match ty with None -> "mono" | Some ty -> Nt.layout ty))
      props
  in
  List.map snd props

let emp = StrMap.empty

let find_axioms asys (task, query) =
  let query_preds = StrSet.of_list @@ get_fv_preds_from_prop query in
  let query_preds = pred_extension (task, query_preds) in
  let axiom1 =
    match task with None -> [] | Some task -> find_axioms_by_task asys task
  in
  ( ZUtilsLog.axiom @@ fun () ->
    Pp.printf "@{<bold>%s@}: %s\n"
      (layout_option (fun x -> x) task)
      (StrList.to_string @@ StrSet.to_list query_preds) );
  let axiom2 = find_axioms_by_preds asys query_preds in
  let axioms = List.slow_rm_dup String.equal (axiom1 @ axiom2) in
  let () =
    ZUtilsLog.axiom @@ fun () ->
    Pp.printf "@{<bold>Axioms by pred: @} %s\n" @@ StrList.to_string axiom2
  in
  let () =
    ZUtilsLog.axiom @@ fun () ->
    Pp.printf "@{<bold>Axioms: @} %s\n" @@ StrList.to_string axioms
  in
  let props =
    StrMap.filter (fun name _ -> List.exists (String.equal name) axioms) asys
  in
  let axioms = gather_indicator_types query (StrMap.to_kv_list props) in
  axioms
