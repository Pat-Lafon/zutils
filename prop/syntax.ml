include Ast
open Sugar

(** constant *)

let constant_to_nt c =
  let open Nt in
  match c with
  | U -> unit_ty
  | B _ -> bool_ty
  | I _ -> int_ty
  | C _ -> char_ty
  | S _ -> string_ty
  | F _ -> float_ty

(** op *)

(* NOTE: there are several constructors cannot be parsed directly from the external files *)
let dt_name_for_typectx = function
  | "()" -> "TT"
  | "::" -> "Cons"
  | "[]" -> "Nil"
  | _ as s -> s

let op_name_for_typectx = function
  | PrimOp name -> name
  | DtConstructor name -> dt_name_for_typectx name

let is_dt_op str =
  let fst_char = String.get str 0 in
  Char.equal (Char.uppercase_ascii fst_char) fst_char

let id_eq_op = function PrimOp "==" -> true | _ -> false
let id_is_dt name = String.(equal name @@ capitalize_ascii name)
let mk_eq_op = PrimOp eq_op
let typed_eq_op_string ty = eq_op#:Nt.(mk_arr ty (mk_arr ty bool_ty))
let mk_tuple_lit lits = (ATu lits)#:(Nt.Ty_tuple (List.map _get_ty lits))
let tvar_to_lit var = (AVar var)#:var.ty
let mk_nth_lit loc lit n = (AProj (lit, n))#:(Nt.get_nth_ty loc lit.ty n)

(** lit *)

let rec fold_lit f acc (lit_e : 't lit) =
  let acc = f acc lit_e in
  match lit_e with
  | AC _ | AVar _ -> acc
  | ATu l | AAppOp (_, l) -> List.fold_left (typed_fold_lit f) acc l
  | AProj (t, _) | AField (t, _) -> typed_fold_lit f acc t
  | ARecord l -> List.fold_left (fun acc (_, t) -> typed_fold_lit f acc t) acc l

and typed_fold_lit f acc (lit_e : ('t, 't lit) typed) = fold_lit f acc lit_e.x

let fv_lit (lit_e : 't lit) =
  List.rev
  @@ fold_lit (fun acc -> function AVar v -> v :: acc | _ -> acc) [] lit_e

let typed_fv_lit (lit_e : ('t, 't lit) typed) = fv_lit lit_e.x

let rec subst_lit (string_x : string) f (lit_e : 't lit) =
  match lit_e with
  | AC constant0 -> AC constant0
  | AVar _t_stringtyped0 ->
      if String.equal _t_stringtyped0.x string_x then f _t_stringtyped0
      else AVar _t_stringtyped0
  | ATu _t__tlittypedlist0 ->
      ATu (List.map (typed_subst_lit string_x f) _t__tlittypedlist0)
  | AProj (_t__tlittyped0, int1) ->
      AProj (typed_subst_lit string_x f _t__tlittyped0, int1)
  | ARecord _t__tlittypedlist0 ->
      ARecord
        (List.map
           (fun (fd, lit) -> (fd, typed_subst_lit string_x f lit))
           _t__tlittypedlist0)
  | AField (_t__tlittyped0, int1) ->
      AField (typed_subst_lit string_x f _t__tlittyped0, int1)
  | AAppOp (_t_stringtyped0, _t__tlittypedlist1) ->
      AAppOp
        ( _t_stringtyped0,
          List.map (typed_subst_lit string_x f) _t__tlittypedlist1 )

and typed_subst_lit (string_x : string) f (lit_e : ('t, 't lit) typed) =
  lit_e#->(subst_lit string_x f)

let rec map_op f (lit_e : 't lit) =
  match lit_e with
  | AC _ | AVar _ -> lit_e
  | ATu l -> ATu (List.map (typed_map_op f) l)
  | AProj (lit, n) -> AProj (typed_map_op f lit, n)
  | ARecord l ->
      ARecord (List.map (fun (fd, lit) -> (fd, typed_map_op f lit)) l)
  | AField (lit, fd) -> AField (typed_map_op f lit, fd)
  | AAppOp (op, args) -> AAppOp (op#->f, List.map (typed_map_op f) args)

and typed_map_op f (lit_e : ('t, 't lit) typed) = lit_e#->(map_op f)

let rec map_lit : 't 's. ('t -> 's) -> 't lit -> 's lit =
 fun f lit_e ->
  match lit_e with
  | AC constant0 -> AC constant0
  | AVar _t_stringtyped0 -> AVar _t_stringtyped0#=>f
  | ATu _t__tlittypedlist0 ->
      ATu (List.map (fun e -> typed_map_lit f e) _t__tlittypedlist0)
  | AProj (_t__tlittyped0, int1) -> AProj (typed_map_lit f _t__tlittyped0, int1)
  | ARecord _t__tlittypedlist0 ->
      ARecord
        (List.map (fun (fd, e) -> (fd, typed_map_lit f e)) _t__tlittypedlist0)
  | AField (_t__tlittyped0, int1) ->
      AField (typed_map_lit f _t__tlittyped0, int1)
  | AAppOp (_t_stringtyped0, _t__tlittypedlist1) ->
      AAppOp (_t_stringtyped0#=>f, List.map (typed_map_lit f) _t__tlittypedlist1)

and typed_map_lit :
    't 's. ('t -> 's) -> ('t, 't lit) typed -> ('s, 's lit) typed =
 fun f lit_e -> lit_e#->(map_lit f)#=>f

let fv_lit_id e = fv_typed_id_to_id fv_lit e
let typed_fv_lit_id e = fv_typed_id_to_id typed_fv_lit e
let subst_lit_instance x instance e = subst_f_to_instance subst_lit x instance e

let typed_subst_lit_instance x instance e =
  subst_f_to_instance typed_subst_lit x instance e

(* force *)
let typed_lit_force_aappop_opt (lit, op) =
  match lit.x with
  | AAppOp ({ x; _ }, args) when String.equal x op -> Some args
  | _ -> None

let typed_lit_force_avar_opt lit =
  match lit.x with AVar id -> Some id | _ -> None

let typed_lit_force_ac_opt lit = match lit.x with AC c -> Some c | _ -> None
let mk_lit_true = AC (B true)
let mk_lit_false = AC (B false)

(** For Nt.t typed *)

let lit_to_nt = function
  | AC c -> constant_to_nt c
  | AVar x -> x.ty
  | ATu l -> Nt.Ty_tuple (List.map _get_ty l)
  | AProj (lit, i) -> (
      match lit.ty with Nt.Ty_tuple l -> List.nth l i | _ -> _die [%here])
  | ARecord l -> Nt.mk_record None (List.map (fun (x, lit) -> x#:lit.ty) l)
  | AField (lit, i) ->
      let l = Nt.as_record [%here] lit.ty in
      let x =
        Zdatatype.List.find __FUNCTION__ (fun x -> String.equal x.x i) l
      in
      x.ty
  | AAppOp (f, _) -> snd @@ Nt.destruct_arr_tp f.ty

let lit_to_tlit lit = lit#:(lit_to_nt lit)

let mk_lit_eq_lit loc lx ly =
  _assert loc "arguments of == should be the same"
    (Nt.equal_nt (lit_to_nt lx) (lit_to_nt ly));
  let ty = lit_to_nt lx in
  AAppOp (typed_eq_op_string ty, [ lx#:ty; ly#:ty ])

let mk_var_eq_var loc x y = mk_lit_eq_lit loc (AVar x) (AVar y)
let mk_var_eq_c loc x c = mk_lit_eq_lit loc (AVar x) (AC c)

let mk_int_l1_eq_l2 l1 l2 =
  AAppOp (typed_eq_op_string Nt.int_ty, [ l1#:Nt.int_ty; l2#:Nt.int_ty ])

let get_var_opt = function AVar x -> Some x | _ -> None

let get_subst_pair a b =
  match get_var_opt a with Some a -> [ (a, b) ] | None -> []

let get_eqlits lit =
  match lit with
  | AAppOp (op, [ a; b ]) when String.equal eq_op op.x ->
      get_subst_pair a.x b.x @ get_subst_pair b.x a.x
  | _ -> []

let find_assignment_of_intvar lit x =
  match lit with
  | AAppOp (op, [ a; b ]) when String.equal eq_op op.x -> (
      match (a.x, b.x) with
      | AVar y, _ when String.equal x y.x -> Some b.x
      | _, AVar y when String.equal x y.x -> Some a.x
      | _, _ -> None)
  | _ -> None

let rec get_non_unit_lit lit =
  (* let () = *)
  (*   Env.show_log "gather" @@ fun _ -> *)
  (*   Printf.printf ">>>>> get_non_unit_lit: %s\n" *)
  (*     (Sexplib.Sexp.to_string (sexp_of_lit lit.x)) *)
  (* in *)
  if Nt.equal_nt Nt.unit_ty lit.ty then None
  else
    match lit.x with
    | AAppOp (_, args) -> (
        (* let () = *)
        (*   Env.show_log "gather" @@ fun _ -> *)
        (*   Printf.printf ">>>>> %s: %s\n" (Op.to_string op.x) *)
        (*     (List.split_by_comma (fun x -> layout x.ty) args) *)
        (* in *)
        let res = List.filter_map get_non_unit_lit args in
        match res with [] -> None | _ -> Some lit.x)
    | _ -> Some lit.x

let get_op_args lit = match lit with AAppOp (_, args) -> args | _ -> []

(** prop *)

open Ast

let show_lit regex = show_lit (fun _ _ -> ()) regex
let show_prop regex = show_prop (fun _ _ -> ()) regex

let rec fv_prop (prop_e : 't prop) =
  match prop_e with
  | Lit _t__tlittyped0 -> [] @ typed_fv_lit _t__tlittyped0
  | Implies (_tprop0, _tprop1) -> ([] @ fv_prop _tprop1) @ fv_prop _tprop0
  | Ite (_tprop0, _tprop1, _tprop2) ->
      (([] @ fv_prop _tprop2) @ fv_prop _tprop1) @ fv_prop _tprop0
  | Not _tprop0 -> [] @ fv_prop _tprop0
  | And _tproplist0 -> [] @ List.concat (List.map fv_prop _tproplist0)
  | Or _tproplist0 -> [] @ List.concat (List.map fv_prop _tproplist0)
  | Iff (_tprop0, _tprop1) -> ([] @ fv_prop _tprop1) @ fv_prop _tprop0
  | Forall { qv; body } ->
      Zdatatype.List.substract (eq_typed String.equal)
        ([] @ fv_prop body)
        [ qv ]
  | Exists { qv; body } ->
      Zdatatype.List.substract (eq_typed String.equal)
        ([] @ fv_prop body)
        [ qv ]

and typed_fv_prop (prop_e : ('t, 't prop) typed) = fv_prop prop_e.x

let rec subst_prop (string_x : string) f (prop_e : 't prop) =
  match prop_e with
  | Lit _t__tlittyped0 -> Lit (typed_subst_lit string_x f _t__tlittyped0)
  | Implies (_tprop0, _tprop1) ->
      Implies (subst_prop string_x f _tprop0, subst_prop string_x f _tprop1)
  | Ite (_tprop0, _tprop1, _tprop2) ->
      Ite
        ( subst_prop string_x f _tprop0,
          subst_prop string_x f _tprop1,
          subst_prop string_x f _tprop2 )
  | Not _tprop0 -> Not (subst_prop string_x f _tprop0)
  | And _tproplist0 -> And (List.map (subst_prop string_x f) _tproplist0)
  | Or _tproplist0 -> Or (List.map (subst_prop string_x f) _tproplist0)
  | Iff (_tprop0, _tprop1) ->
      Iff (subst_prop string_x f _tprop0, subst_prop string_x f _tprop1)
  | Forall { qv; body } ->
      if String.equal qv.x string_x then Forall { qv; body }
      else Forall { qv; body = subst_prop string_x f body }
  | Exists { qv; body } ->
      if String.equal qv.x string_x then Exists { qv; body }
      else Exists { qv; body = subst_prop string_x f body }

and typed_subst_prop (string_x : string) f (prop_e : ('t, 't prop) typed) =
  prop_e#->(subst_prop string_x f)

let rec map_prop (f : 't -> 's) (prop_e : 't prop) =
  match prop_e with
  | Lit _t__tlittyped0 -> Lit (typed_map_lit f _t__tlittyped0)
  | Implies (_tprop0, _tprop1) ->
      Implies (map_prop f _tprop0, map_prop f _tprop1)
  | Ite (_tprop0, _tprop1, _tprop2) ->
      Ite (map_prop f _tprop0, map_prop f _tprop1, map_prop f _tprop2)
  | Not _tprop0 -> Not (map_prop f _tprop0)
  | And _tproplist0 -> And (List.map (map_prop f) _tproplist0)
  | Or _tproplist0 -> Or (List.map (map_prop f) _tproplist0)
  | Iff (_tprop0, _tprop1) -> Iff (map_prop f _tprop0, map_prop f _tprop1)
  | Forall { qv; body } -> Forall { qv = qv#=>f; body = map_prop f body }
  | Exists { qv; body } -> Exists { qv = qv#=>f; body = map_prop f body }

and typed_map_prop (f : 't -> 's) (prop_e : ('t, 't prop) typed) =
  prop_e#=>f#->(map_prop f)

let fv_prop_id e = fv_typed_id_to_id fv_prop e
let typed_fv_prop_id e = fv_typed_id_to_id typed_fv_prop e

let subst_prop_instance x instance e =
  subst_f_to_instance subst_prop x instance e

let typed_subst_prop_instance x instance e =
  subst_f_to_instance typed_subst_prop x instance e

(* force *)
let prop_force_typed_lit_opt prop =
  match prop with Lit lit -> Some lit | _ -> None

let rec get_cbool prop =
  match prop with
  | Lit { x = AC (B b); _ } -> Some b
  | Not p ->
      let* p = get_cbool p in
      Some (not p)
  | _ -> None

let smart_not prop =
  match get_cbool prop with
  | Some p -> Lit (AC (B (not p)))#:Nt.bool_ty
  | None -> ( match prop with Not p -> p | _ -> Not prop)

let mk_true = Lit (AC (B true))#:Nt.bool_ty
let mk_false = Lit (AC (B false))#:Nt.bool_ty
let is_true p = match get_cbool p with Some true -> true | _ -> false
let is_false p = match get_cbool p with Some false -> true | _ -> false

(* let rec is_true p = *)
(*   match p with *)
(*   | Not p -> is_false p *)
(*   | _ -> ( *)
(*       match get_cbool p with *)
(*       | Some true -> true *)
(*       | Some false -> false *)
(*       | None -> false) *)

(* and is_false p = *)
(*   match p with *)
(*   | Not p -> is_true p *)
(*   | _ -> ( match get_cbool p with Some false -> true | _ -> false) *)

open Zdatatype

let unfold_and prop =
  let rec aux = function
    | [] -> []
    | And l :: l' -> aux (l @ l')
    | prop :: l' -> prop :: aux l'
  in
  let l = aux prop in
  List.slow_rm_dup eq_prop l

let smart_and l =
  let l = unfold_and l in
  if List.exists is_false l then mk_false
  else
    match List.filter (fun p -> not (is_true p)) l with
    | [] -> mk_true
    | [ x ] -> x
    | l -> And l

let unfold_or prop =
  let rec aux = function
    | [] -> []
    | Or l :: l' -> aux (l @ l')
    | prop :: l' -> prop :: aux l'
  in
  let l = aux prop in
  List.slow_rm_dup eq_prop l

let smart_or l =
  let l = unfold_or l in
  if List.exists is_true l then mk_true
  else
    match List.filter (fun p -> not (is_false p)) l with
    | [] -> mk_false
    | [ x ] -> x
    | l -> Or l

let smart_add_to (a : 't prop) (prop : 't prop) =
  match get_cbool a with
  | Some true -> prop
  | Some false -> mk_false
  | None -> (
      match prop with
      | And props -> smart_and (a :: props)
      | _ -> smart_and [ a; prop ])

let smart_implies a prop =
  match get_cbool a with
  | Some true -> prop
  | Some false -> mk_true
  | None -> (
      match get_cbool prop with
      | Some true -> mk_true
      | Some false -> smart_not a
      | None -> Implies (a, prop))

let smart_iff p1 p2 =
  if eq_prop p1 p2 then mk_true
  else
    match (get_cbool p1, get_cbool p2) with
    | Some b1, Some b2 -> if Bool.equal b1 b2 then mk_true else mk_false
    | _, _ -> Iff (p1, p2)

let str_in_list x l = List.exists (String.equal x) l

let smart_forall qvs prop =
  let fvs = fv_prop_id prop in
  let qvs = List.filter (fun x -> str_in_list x.x fvs) qvs in
  List.fold_right (fun qv body -> Forall { qv; body }) qvs prop

let smart_exists qvs prop =
  let fvs = fv_prop_id prop in
  let qvs = List.filter (fun x -> str_in_list x.x fvs) qvs in
  List.fold_right (fun qv body -> Exists { qv; body }) qvs prop

let get_lits prop =
  let rec aux e res =
    match e with
    | Lit { x = AC _; _ } -> res
    | Lit lit -> (
        let litopt = get_non_unit_lit lit in
        match litopt with None -> res | Some lit -> lit :: res)
    | Implies (e1, e2) -> aux e1 @@ aux e2 res
    | Ite (e1, e2, e3) -> aux e1 @@ aux e2 @@ aux e3 res
    | Not e -> aux e res
    | And es -> List.fold_right aux es res
    | Or es -> List.fold_right aux es res
    | Iff (e1, e2) -> aux e1 @@ aux e2 res
    | Forall _ -> _die [%here]
    | Exists _ -> _die [%here]
  in
  let (lits : Nt.t lit list) = aux prop [] in
  (* let () = *)
  (*   Printf.printf ">>>>> get_lits: %s\n" *)
  (*     (List.split_by_comma layout_sexp_lit lits) *)
  (* in *)
  Zdatatype.List.slow_rm_dup eq_lit lits

let build_euf vars =
  let space = Hashtbl.create 10 in
  let () =
    List.iter
      (fun { x; ty } ->
        match Hashtbl.find_opt space ty with
        | None -> Hashtbl.add space ty [ x ]
        | Some l -> Hashtbl.replace space ty (x :: l))
      vars
  in
  let aux vars =
    let pairs = List.combination_l vars 2 in
    let eqlits =
      List.map
        (fun l ->
          match l with
          | [ x; y ] -> mk_lit_eq_lit [%here] x y
          | _ -> _die [%here])
        pairs
    in
    eqlits
  in
  let res = Hashtbl.fold (fun _ vars res -> aux vars @ res) space [] in
  res

(** sevent *)

(* subst *)

(* normalize name *)

(* let normalize_name = function *)
(*   | GuardEvent { vs; phi } -> *)
(*       let vs' = vs_names (List.length vs) in *)
(*       let tmp = _safe_combine [%here] vs vs' in *)
(*       let phi = *)
(*         List.fold_left *)
(*           (fun phi (x', x) -> subst_prop_instance x'.x (AVar x #: x'.ty) phi) *)
(*           phi tmp *)
(*       in *)
(*       let vs = List.map (fun (x', x) -> x #: x'.ty) tmp in *)
(*       GuardEvent { vs; phi } *)
(*   | EffEvent { op; vs; phi } -> *)
(*       let vs' = vs_names (List.length vs) in *)
(*       let tmp = _safe_combine [%here] vs vs' in *)
(*       let phi = *)
(*         List.fold_left *)
(*           (fun phi (x', x) -> subst_prop_instance x'.x (AVar x #: x'.ty) phi) *)
(*           phi tmp *)
(*       in *)
(*       let vs = List.map (fun (x', x) -> x #: x'.ty) tmp in *)
(*       EffEvent { op; vs; phi } *)

(* gather lits *)
(** For Nt.t typed*)

open Zdatatype

type gathered_lits = {
  global_lits : Nt.t lit list;
  local_lits : ((Nt.t, string) typed list * Nt.t lit list) StrMap.t;
}

let gathered_lits_init () = { global_lits = []; local_lits = StrMap.empty }

let gathered_rm_dup { global_lits; local_lits } =
  let global_lits = List.slow_rm_dup eq_lit global_lits in
  let local_lits =
    StrMap.map (fun (vs, lits) -> (vs, List.slow_rm_dup eq_lit lits)) local_lits
  in
  { global_lits; local_lits }

let rec get_consts_from_lit = function
  | AAppOp (_, args) -> List.concat_map get_consts_from_typed_lit args
  | AC c -> [ c ]
  | _ -> []

and get_consts_from_typed_lit lit = get_consts_from_lit lit.x

let get_consts prop =
  let lits = get_lits prop in
  let cs = List.concat_map get_consts_from_lit lits in
  List.slow_rm_dup equal_constant cs

let lit_to_prop lit = Lit lit#:(lit_to_nt lit)
let msubst f = List.fold_right (fun (x, lit) -> f x lit)
let subst_name_qv x z y = if String.equal y.x x then z else y

let to_conjs prop =
  let rec aux = function And l -> List.concat_map aux l | _ as r -> [ r ] in
  aux prop

let to_lit_opt = function Lit lit -> Some lit.x | _ -> None
let is_var_c = function AVar _ | AC _ -> true | _ -> false

let simp_eq_lit lit =
  match lit with
  | AAppOp (op, [ a; b ]) when String.equal eq_op op.x ->
      if equal_lit Nt.equal_nt a.x b.x then AC (B true) else lit
  | _ -> lit

let is_eq_phi x phi =
  match phi with
  | Lit lit -> (
      match lit.x with
      | AAppOp (op, [ a; b ]) when String.equal eq_op op.x ->
          if equal_lit Nt.equal_nt a.x (AVar x) then Some b.x
          else if equal_lit Nt.equal_nt b.x (AVar x) then Some a.x
          else None
      | _ -> None)
  | _ -> None

let smart_forall_phi (x, phi) query =
  match is_eq_phi x phi with
  | None -> smart_forall [ x ] (smart_implies phi query)
  | Some lit -> subst_prop_instance x.x lit query

let smart_exists_phi (x, phi) query =
  match is_eq_phi x phi with
  | None -> smart_exists [ x ] (smart_add_to phi query)
  | Some lit -> subst_prop_instance x.x lit query

(* let rec has_top_ex phi = *)
(*   match phi with *)
(*   | Exists _ -> true *)
(*   | And ps -> List.exists has_top_ex ps *)
(*   | Lit _ | Implies _ | Ite _ | Not _ | Or _ | Iff _ | Forall _ -> false *)

let lift_ex_quantifiers phi =
  let rec aux qvs prop =
    match prop with
    | Exists { qv; body } -> aux (qvs @ [ qv ]) body
    (* | And [] -> _die [%here] *)
    (* | And [p1] -> aux qvs p1 *)
    | And ps ->
        let qvss, ps = List.split @@ List.map (aux []) ps in
        let qvs = qvs @ List.concat qvss in
        (qvs, And ps)
    | Lit _ | Implies _ | Ite _ | Not _ | Or _ | Iff _ | Forall _ -> (qvs, prop)
  in
  aux [] phi

let simpl_eq_in_prop =
  let rec aux = function
    | Lit lit -> Lit (simp_eq_lit lit.x)#:lit.ty
    | Implies (e1, e2) when equal_prop Nt.equal_nt e1 e2 -> mk_true
    | Implies (e1, e2) -> Implies (aux e1, aux e2)
    | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
    | Not p ->
        let p = aux p in
        if is_true p then mk_false else if is_false p then mk_true else Not p
    | And es -> smart_and (List.map aux es)
    | Or es -> smart_or (List.map aux es)
    | Iff (e1, e2) when equal_prop Nt.equal_nt e1 e2 -> mk_true
    | Iff (e1, e2) -> Iff (aux e1, aux e2)
    | Forall { qv; body } -> Forall { qv; body = aux body }
    | Exists { qv; body } -> Exists { qv; body = aux body }
  in
  aux

let tv_mem vs qv = List.exists (fun x -> String.equal x.x qv.x) vs
let tv_not_mem vs qv = not (tv_mem vs qv)
let tv_to_lit x = (AVar x)#:x.ty
let c_to_lit c = (AC c)#:(constant_to_nt c)

(* let fresh_name_lit = *)
(*   let rec aux lit = *)
(*     match lit with *)
(*     | AC _ | AVar _ -> lit *)
(*     | ATu l -> ATu (List.map typed_aux l) *)
(*     | AProj (lit, i) -> AProj (typed_aux lit, i) *)
(*     | ARecord l -> ARecord (List.map (fun (x, lit) -> (x, typed_aux lit)) l) *)
(*     | AField (lit, i) -> AField (typed_aux lit, i) *)
(*     | AAppOp (f, args) -> AAppOp (f, List.map typed_aux args) *)
(*   and typed_aux lit = lit#->aux in *)
(*   typed_aux *)

let fresh_name_prop =
  let rec aux = function
    | Lit lit -> Lit lit
    | Implies (e1, e2) -> Implies (aux e1, aux e2)
    | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
    | Not p -> Not (aux p)
    | And es -> smart_and (List.map aux es)
    | Or es -> smart_or (List.map aux es)
    | Iff (e1, e2) -> Iff (aux e1, aux e2)
    | Forall { qv; body } ->
        let qv' = qv#->Rename.unique_var in
        let body = subst_prop_instance qv.x (AVar qv') body in
        Forall { qv = qv'; body = aux body }
    | Exists { qv; body } ->
        let qv' = qv#->Rename.unique_var in
        let body = subst_prop_instance qv.x (AVar qv') body in
        Exists { qv = qv'; body = aux body }
  in
  aux

let count_prop_qv =
  let rec aux = function
    | Lit _ -> (0, 0)
    | Implies (e1, e2) ->
        let num_ex1, num_fa1 = aux e1 in
        let num_fa2, num_ex2 = aux e2 in
        (num_fa1 + num_fa2, num_ex1 + num_ex2)
    | Ite (e1, e2, e3) ->
        let num_fa1, num_ex1 = aux e1 in
        let num_fa2, num_ex2 = aux e2 in
        let num_ex3, num_fa3 = aux e3 in
        (num_fa1 + num_fa2 + num_fa3, num_ex1 + num_ex2 + num_ex3)
    | Not e1 ->
        let num_fa1, num_ex1 = aux e1 in
        (num_fa1, num_ex1)
    | And es ->
        let num_fas, num_exs = List.split @@ List.map aux es in
        (List.fold_left ( + ) 0 num_fas, List.fold_left ( + ) 0 num_exs)
    | Or es ->
        let num_fas, num_exs = List.split @@ List.map aux es in
        (List.fold_left ( + ) 0 num_fas, List.fold_left ( + ) 0 num_exs)
    | Iff (e1, e2) ->
        let num_ex1, num_fa1 = aux e1 in
        let num_fa2, num_ex2 = aux e2 in
        (num_fa1 + num_fa2, num_ex1 + num_ex2)
    | Forall { body; _ } ->
        let num_fa1, num_ex1 = aux body in
        (num_fa1 + 1, num_ex1)
    | Exists { body; _ } ->
        let num_fa1, num_ex1 = aux body in
        (num_fa1, num_ex1 + 1)
  in
  aux

let count_pred_lit lit =
  let rec aux lit =
    match lit with
    | AC _ | AVar _ -> []
    | ATu l -> List.concat_map typed_aux l
    | AProj (lit, _) -> typed_aux lit
    | ARecord l -> List.concat_map (fun (_, lit) -> typed_aux lit) l
    | AField (lit, _) -> typed_aux lit
    | AAppOp (f, args) ->
        let preds = if is_builtin_op f.x then [] else [ f ] in
        preds @ List.concat_map typed_aux args
  and typed_aux lit = aux lit.x in
  List.slow_rm_dup (fun x y -> String.equal x.x y.x) @@ typed_aux lit

let count_pred_prop prop =
  let rec aux = function
    | Lit lit -> count_pred_lit lit
    | Implies (e1, e2) -> List.concat_map aux [ e1; e2 ]
    | Ite (e1, e2, e3) -> List.concat_map aux [ e1; e2; e3 ]
    | Not e1 -> aux e1
    | And es -> List.concat_map aux es
    | Or es -> List.concat_map aux es
    | Iff (e1, e2) -> List.concat_map aux [ e1; e2 ]
    | Forall { body; _ } -> aux body
    | Exists { body; _ } -> aux body
  in
  List.slow_rm_dup (fun x y -> String.equal x.x y.x) @@ aux prop

(** Poly *)

let gather_poly_preds_from_prop prop =
  let rec aux = function
    | Lit lit -> ( match lit.x with AAppOp (op, _) -> [ op ] | _ -> [])
    | Implies (e1, e2) -> aux e1 @ aux e2
    | Ite (e1, e2, e3) -> aux e1 @ aux e2 @ aux e3
    | Not e -> aux e
    | And es -> List.concat @@ List.map aux es
    | Or es -> List.concat @@ List.map aux es
    | Iff (e1, e2) -> aux e1 @ aux e2
    | Forall { body; _ } -> aux body
    | Exists { body; _ } -> aux body
  in
  let xs = aux prop in
  List.slow_rm_dup (fun x y -> String.equal x.x y.x) xs

let rename_pred_prop oldname newname =
  let rec aux = function
    | Lit lit -> (
        match lit.x with
        | AAppOp (op, args) when String.equal op.x oldname ->
            Lit (AAppOp (newname#:op.ty, args))#:lit.ty
        | _ -> Lit lit)
    | Implies (e1, e2) -> Implies (aux e1, aux e2)
    | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
    | Not p -> Not (aux p)
    | And es -> smart_and (List.map aux es)
    | Or es -> smart_or (List.map aux es)
    | Iff (e1, e2) -> Iff (aux e1, aux e2)
    | Forall { qv; body } -> Forall { qv; body = aux body }
    | Exists { qv; body } -> Exists { qv; body = aux body }
  in
  aux

(** Z3 *)

let get_tfv_preds_from_lit lit =
  let rec aux = function
    | AC _ | AVar _ -> []
    | ATu l -> List.concat_map (fun x -> aux x.x) l
    | AProj (lit, _) -> aux lit.x
    | ARecord l -> List.concat_map (fun (_, x) -> aux x.x) l
    | AField (lit, _) -> aux lit.x
    | AAppOp (f, args) -> f :: List.concat_map (fun x -> aux x.x) args
  in
  List.slow_rm_dup (equal_typed Nt.equal_nt String.equal) @@ aux lit.x

let get_tfv_preds_from_prop prop =
  let rec aux = function
    | Lit lit -> get_tfv_preds_from_lit lit
    | Implies (e1, e2) -> List.concat_map aux [ e1; e2 ]
    | Ite (e1, e2, e3) -> List.concat_map aux [ e1; e2; e3 ]
    | Not e -> aux e
    | And es -> List.concat_map aux es
    | Or es -> List.concat_map aux es
    | Iff (e1, e2) -> List.concat_map aux [ e1; e2 ]
    | Forall { body; _ } -> aux body
    | Exists { body; _ } -> aux body
  in
  let res =
    List.slow_rm_dup (equal_typed Nt.equal_nt String.equal) @@ aux prop
  in
  List.filter (fun p -> not (is_builtin_op p.x)) res

let get_fv_preds_from_lit lit = List.map _get_x @@ get_tfv_preds_from_lit lit

let get_fv_preds_from_prop prop =
  List.map _get_x @@ get_tfv_preds_from_prop prop

let to_nnf prop =
  let rec aux is_negate prop =
    match prop with
    | Lit _ -> if is_negate then Not prop else prop
    | Implies (e1, e2) ->
        if is_negate then smart_and [ e1; aux true e2 ]
        else Implies (aux false e1, aux false e2)
    | Ite _ | Iff _ -> if is_negate then smart_not prop else prop
    | Not p -> aux (not is_negate) p
    | And es ->
        if is_negate then smart_or (List.map (aux true) es)
        else smart_and (List.map (aux false) es)
    | Or es ->
        if is_negate then smart_and (List.map (aux true) es)
        else smart_or (List.map (aux false) es)
    | Forall { qv; body } ->
        if is_negate then Exists { qv; body = aux true body }
        else Forall { qv; body = aux false body }
    | Exists { qv; body } ->
        if is_negate then Forall { qv; body = aux true body }
        else Exists { qv; body = aux false body }
  in
  let res = aux false prop in
  res

let snf_quantified_var_by_name name =
  let rec aux prop =
    match prop with
    | Exists { body; qv } ->
        let body = aux body in
        if String.equal qv.x name then body else Exists { body; qv }
    | Forall { body; qv } ->
        let body = aux body in
        if String.equal qv.x name then body else Forall { body; qv }
    | And l -> smart_and (List.map aux l)
    | Or l -> smart_or (List.map aux l)
    | Implies (e1, e2) -> Implies (aux e1, aux e2)
    | Lit _ -> prop
    | Iff (e1, e2) -> Iff (aux e1, aux e2)
    | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
    | Not e -> Not (aux e)
  in
  aux
