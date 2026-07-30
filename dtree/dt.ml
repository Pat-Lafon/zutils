module type Predictable = sig
  type lit
  type prop

  val mk_true : prop
  val mk_false : prop
  val mk_lit : lit -> prop
  val mk_ite : lit -> prop -> prop -> prop
  val mk_and : prop -> prop -> prop
  val mk_or : prop -> prop -> prop
  val mk_not : prop -> prop
  val layout_lit : lit -> string
  val layout_prop : prop -> string
end

module F (P : Predictable) = struct
  open P
  open Sugar
  open Zdatatype

  type features = lit array
  type label = Pos | Neg | MayNeg
  type fvtab = (bool list, label) Hashtbl.t
  type t = T | F | Node of int * t * t

  let layout_label = function Pos -> "pos" | Neg -> "neg" | MayNeg -> "mayneg"

  let rec layout = function
    | T -> "⊤"
    | F -> "⊥"
    | Node (feature, l, r) -> spf "[%i](%s,%s)" feature (layout l) (layout r)

  (** prune out unreachable path in the DT. we will simplify Node(id, F, F) as F
      we don't simplify Node(id, T, T) as T, which lose information *)
  let refine_dt_under_prop (sat_solver : prop -> bool) prop (features, dt) =
    let counter = ref 0 in
    let sat_solver prop =
      counter := !counter + 1;
      sat_solver prop
    in
    let rec aux prop dt =
      if not (sat_solver prop) then F
      else
        match dt with
        | T -> T
        | F -> F
        | Node (idx, dt_t, dt_f) -> (
            let lit = features.(idx) in
            let prop_t = mk_and (mk_lit lit) prop in
            let prop_f = mk_and (mk_not (mk_lit lit)) prop in
            match (aux prop_t dt_t, aux prop_f dt_f) with
            | F, F -> F
            | dt_t, dt_f -> Node (idx, dt_t, dt_f))
    in
    let res = aux prop dt in
    (!counter, res)

  let mk_complete_dt features =
    let rec aux idx =
      if idx >= Array.length features then T
      else Node (idx, aux (idx + 1), aux (idx + 1))
    in
    aux 0

  (** Define a pruned DT. *)
  let init_pruned_dt (sat_solver : prop -> bool) features =
    let dt = mk_complete_dt features in
    refine_dt_under_prop sat_solver mk_true (features, dt)

  let lits_to_tab l =
    let tab = Hashtbl.create (List.length l) in
    List.iter (fun (lit, b) -> Hashtbl.add tab lit b) l;
    tab

  (** Convert dt into reachable paths. *)
  let dt_to_paths (features, dt) =
    let rec aux prefix dt =
      match dt with
      | T -> [ prefix ]
      | F -> []
      | Node (idx, dt_t, dt_f) ->
          let lit = features.(idx) in
          aux ((lit, true) :: prefix) dt_t @ aux ((lit, false) :: prefix) dt_f
    in
    let res = aux [] dt in
    let res = List.mapi (fun idx x -> (idx, lits_to_tab x)) res in
    res

  let mk_feature_tab features =
    Hashtbl.of_seq
    @@ Seq.mapi (fun id lit -> (lit, id))
    @@ Array.to_seq features

  (** Remove unreachable paths by given paths *)
  let refine_dt_from_tab features (paths : ('a, bool) Hashtbl.t list) dt =
    let rec aux paths dt =
      if 0 == List.length paths then F
      else
        match dt with
        | T -> T
        | F -> F
        | Node (idx, dt_t, dt_f) -> (
            let lit = features.(idx) in
            let paths_t, paths_f =
              List.partition (fun h -> Hashtbl.find h lit) paths
            in
            match (aux paths_t dt_t, aux paths_f dt_f) with
            | F, F -> F
            | T, T -> T
            | dt_t, dt_f -> Node (idx, dt_t, dt_f))
    in
    aux paths dt

  let eq_label a b =
    match (a, b) with
    | Pos, Pos | Neg, Neg | MayNeg, MayNeg -> true
    | _ -> false

  let init_fvtab features =
    let len = Array.length features in
    let init_fv = List.init len (fun _ -> false) in
    let rec next fv =
      match fv with
      | [] -> None
      | false :: fv -> Some (true :: fv)
      | true :: fv ->
          let* fv = next fv in
          Some (false :: fv)
    in
    let fvtab = Hashtbl.create (pow 2 (Array.length features)) in
    let rec loop fv =
      Hashtbl.add fvtab fv MayNeg;
      match next fv with None -> () | Some fv' -> loop fv'
    in
    let () = loop init_fv in
    fvtab

  let layout_raw_fv fv = List.split_by ";" (fun b -> spf "%b" b) fv

  let layout_fv features fv =
    let props =
      List.mapi
        (fun id b ->
          let lit = features.(id) in
          spf "%s:%b" (layout_lit lit) b)
        fv
    in
    List.split_by "; " (fun x -> x) props

  let pprint_fvtab features fvtab =
    Hashtbl.iter
      (fun fv label ->
        Printf.printf "[%s] %s\n" (layout_label label) (layout_fv features fv))
      fvtab

  let pick_by_label fvtab lab =
    Hashtbl.fold
      (fun fv label res ->
        match res with
        | None -> if eq_label label lab then Some fv else None
        | Some fv -> Some fv)
      fvtab None

  let label_as fvtab fv label = Hashtbl.replace fvtab fv label

  let simp_dt dt =
    let rec aux dt =
      match dt with
      | T | Node (_, T, T) -> T
      | F | Node (_, F, F) -> F
      | Node (id, dt_l, dt_r) -> (
          let dt_l, dt_r = map2 aux (dt_l, dt_r) in
          match (dt_l, dt_r) with
          | T, T -> T
          | F, F -> F
          | _, _ -> Node (id, dt_l, dt_r))
    in
    aux dt

  let to_prop (features : lit array) (dt : t) =
    let rec aux dt =
      match dt with
      | T | Node (_, T, T) -> mk_true
      | F | Node (_, F, F) -> mk_false
      | Node (id, T, dt_r) ->
          let prop_r = aux dt_r in
          mk_or (mk_lit (Array.get features id)) prop_r
      | Node (id, dt_l, T) ->
          let prop_l = aux dt_l in
          mk_or (mk_not (mk_lit (Array.get features id))) prop_l
      | Node (id, F, dt_r) ->
          let prop_r = aux dt_r in
          mk_and (mk_not (mk_lit (Array.get features id))) prop_r
      | Node (id, dt_l, F) ->
          let prop_l = aux dt_l in
          mk_and (mk_lit (Array.get features id)) prop_l
      | Node (id, dt_l, dt_r) ->
          let dt_l, dt_r = map2 aux (dt_l, dt_r) in
          mk_ite (Array.get features id) dt_l dt_r
    in
    aux (simp_dt dt)

  let predicate (dt : t) (fv : bool array) =
    let rec aux dt =
      match dt with
      | T -> true
      | F -> false
      | Node (id, l, r) -> if Array.get fv id then aux l else aux r
    in
    aux dt

  let is_not_neg = function Neg -> false | _ -> true

  open FastDT

  let of_fastdt dt =
    let rec aux = function
      | FastDT.Leaf { c_t; c_f } ->
          let res =
            if Float.abs c_t < 1e-3 then F
            else if Float.abs c_f < 1e-3 then T
            else _failatwith [%here] (spf "Bad Dt Result(%f, %f)" c_t c_f)
          in
          res
      | FastDT.Node { split; if_t; if_f } -> Node (split, aux if_t, aux if_f)
    in
    aux dt

  (** The input is a hashtable, which maps bool list into label; by default, all
      bool list are labeled as false (biased as false); The output is a dt. *)
  let biased_classify (len : int) (htab : (bool list, bool) Hashtbl.t) =
    let samples =
      Array.init (pow 2 len) (fun n ->
          (false, Array.of_list (BoolList.of_int len n)))
    in
    let samples =
      Array.map
        (fun (label, l) ->
          match Hashtbl.find_opt htab (Array.to_list l) with
          | None -> (label, l)
          | Some label -> (label, l))
        samples
    in
    (* let () = *)
    (*   Array.iter *)
    (*     (fun (tf, barr) -> *)
    (*       Printf.printf "%b: %s\n" tf *)
    (*         (List.split_by ";" (fun x -> if x then "T" else "F") *)
    (*         @@ Array.to_list barr)) *)
    (*     samples *)
    (* in *)
    let dt = FastDT.make_dt ~samples ~max_d:500 in
    of_fastdt dt

  let classify_as_prop (features : features) (pos : bool list list) =
    let len = Array.length features in
    let htab = Hashtbl.create (List.length pos) in
    let () = List.iter (fun l -> Hashtbl.add htab l true) pos in
    let dt = biased_classify len htab in
    to_prop features dt

  let path_to_pos (features : features) (path : (lit, bool) Hashtbl.t) =
    Array.to_list (Array.map (Hashtbl.find path) features)
end
