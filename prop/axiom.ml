(** Axiom system *)

open Syntax
open Zdatatype
open Sugar

let _log = ZUtilsConfig._log "axiom"

let add_laxiom asys (name, prop) =
  let preds = StrSet.of_list @@ get_fv_preds_from_prop prop in
  if StrMap.mem name asys then
    _die_with [%here] (spf "duplicate axiom name: %s" name)
  else StrMap.add name { preds; prop } asys

let add_laxioms asys l = List.fold_left add_laxiom asys l

let find_axioms_by_preds asys query_preds =
  let m =
    StrMap.filter
      (fun name { preds; _ } ->
        ( _log @@ fun () ->
          Pp.printf "@{<bold>in %s@}: %s\n" name
            (StrList.to_string @@ StrSet.to_list preds) );
        StrSet.subset preds query_preds)
      asys
  in
  StrMap.to_key_list m

(* Single pass, not a fixpoint: a rule fires only if its key is already in [ps]
   when reached, so each rule must list its full transitive closure — under-listing
   silently under-extends. *)
let pred_extension ps =
  let rules =
    List.map
      (fun (k, vs) -> (StrSet.singleton k, vs))
      (ZUtilsConfig.get_pred_extension_rules ())
  in
  List.fold_left
    (fun ps (rname, new_preds) ->
      if StrSet.subset rname ps then StrSet.add_seq (List.to_seq new_preds) ps
      else ps)
    ps rules

let find_first_poly_type_from_axiom prop =
  let rec aux prop =
    match prop with
    | Exists { body; qv } | Forall { body; qv } -> (
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
  let res = aux prop in
  ( _log @@ fun () ->
    match res with
    | None -> Printf.printf "normal type %s\n" (Front.layout_prop prop)
    | Some x ->
        Pp.printf "@{<bold>Axiom Indicator Type %s@} in %s\n" (Nt.layout x.ty)
          (Front.layout_prop prop) );
  Option.map (fun x -> x.ty) res

type inst_res = Mono | NoPoly | PolyAss of Nt.t

let gather_indicator_types query axioms =
  let typed_preds = get_tfv_preds_from_prop query in
  let preds_in_aximos =
    List.fold_left
      (fun s (_, { preds; _ }) -> StrSet.union preds s)
      StrSet.empty axioms
  in
  let relevant_preds =
    List.filter (fun x -> StrSet.mem x.x preds_in_aximos) typed_preds
  in
  (* The concrete types to instantiate each polymorphic axiom at (below): the
     first-argument type of every relevant predicate as it appears in the query.
     Nullary preds contribute nothing. *)
  let indicator_types =
    List.slow_rm_dup Nt.equal_nt
    @@ List.filter_map
         (fun p ->
           match Nt.destruct_arr_tp p.ty with
           | x :: _, _ -> Some x
           | [], _ -> None)
         relevant_preds
  in
  let instantiate_axiom_by_ty ax ax_fst_ty ty =
    let tvars = Nt.gather_type_vars ty in
    let ty =
      List.fold_right (fun id -> Nt.subst_nt (id, Nt.mk_uninterp id)) tvars ty
    in
    let () =
      _log @@ fun () ->
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
            ( _log @@ fun () ->
              Printf.printf
                "Warning: axiom [%s] should at least have one instantiation."
                name );
            []
        | _ -> List.map (fun (ty, prop) -> ((name, Some ty), prop)) l)
  in
  let props = List.concat_map instantiate_axiom axioms in
  let () =
    _log @@ fun () ->
    List.iter
      (fun ((name, ty), _) ->
        Pp.printf "%s::@{<bold>%s@}\n" name
          (match ty with None -> "mono" | Some ty -> Nt.layout ty))
      props
  in
  List.map (fun ((name, _ty), prop) -> (name, prop)) props

let emp = StrMap.empty

(* Like [find_axioms] but unfiltered — every loaded axiom. *)
let all_axioms asys =
  List.map (fun (name, { prop; _ }) -> (name, prop)) (StrMap.to_kv_list asys)

let find_axioms asys query =
  let query_preds = StrSet.of_list @@ get_fv_preds_from_prop query in
  let query_preds = pred_extension query_preds in
  ( _log @@ fun () ->
    Pp.printf "@{<bold>query preds@}: %s\n"
      (StrList.to_string @@ StrSet.to_list query_preds) );
  let axiom2 = find_axioms_by_preds asys query_preds in
  let axiom_set = StrSet.of_list axiom2 in
  let axioms = StrSet.to_list axiom_set in
  let () =
    _log @@ fun () ->
    Pp.printf "@{<bold>Axioms by pred: @} %s\n" @@ StrList.to_string axiom2
  in
  let () =
    _log @@ fun () ->
    Pp.printf "@{<bold>Axioms: @} %s\n" @@ StrList.to_string axioms
  in
  let props = StrMap.filter (fun name _ -> StrSet.mem name axiom_set) asys in
  let axioms = gather_indicator_types query (StrMap.to_kv_list props) in
  axioms
