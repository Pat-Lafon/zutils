open Z3
open Z3.Expr
open Z3.Boolean
open Z3.Arithmetic
open Sugar
open Normalty

let find_const_in_model m x =
  let cs = Z3.Model.get_const_decls m in
  let i =
    List.find_opt
      (fun d ->
        let name = Z3.Symbol.to_string @@ Z3.FuncDecl.get_name d in
        (* let () = Printf.printf "Find (%s) in %s\n" x name in *)
        String.equal name x)
      cs
  in
  match i with
  | Some i ->
      (* let () = Printf.printf "Const %s\n" @@ Z3.FuncDecl.to_string i in *)
      Some (Z3.FuncDecl.apply i [])
  | None -> None

let get_int_by_name m x =
  let i = find_const_in_model m x in
  match i with
  | None -> None
  | Some i -> (
      match Z3.Model.eval m i false with
      (* match Z3.Model.get_const_interp m i with *)
      | None -> _die_with [%here] "get_int"
      | Some v ->
          (* Printf.printf "get_int(%s)\n" (Z3.Expr.to_string v); *)
          Some (int_of_string @@ Z3.Arithmetic.Integer.numeral_to_string v))

let get_string_by_name m x =
  let i = find_const_in_model m x in
  match i with
  | None -> None
  | Some i -> (
      match Z3.Model.eval m i false with
      (* match Z3.Model.get_const_interp m i with *)
      | None -> _die_with [%here] "get_string"
      | Some v ->
          let str = Expr.to_string v in
          let str = List.of_seq @@ String.to_seq str in
          let str = List.filter (fun c -> not (Char.equal c '"')) str in
          let str = String.of_seq @@ List.to_seq str in
          (* Printf.printf "get_int(%s)\n" (Z3.Expr.to_string v); *)
          Some str)

(* let _z3_enum_type = Hashtbl.create 5 *)

(* let get_z3_enum_type ctx (enum_name, enum_elems) = *)
(*   match Hashtbl.find_opt _z3_enum_type enum_name with *)
(*   | Some sort -> sort *)
(*   | None -> *)
(*       let sort = Enumeration.mk_sort_s ctx enum_name enum_elems in *)
(*       Hashtbl.add _z3_enum_type enum_name sort; *)
(*       sort *)

(* let mk_tuple ctx n = Symbol.mk_string ctx (spf "_tuple%i" n) *)
let tuple_field ctx n i = Symbol.mk_string ctx (spf "%s_%i" n i)

open Zdatatype

(* let record_name fields = spf "_record%s" (List.split_by "_" _get_x fields) *)
let mk_recog ctx name = Symbol.mk_string ctx (spf "_is%s" name)
let z3_unit_name = "unit"
let z3_tt_name = "tt"
let mk_some_name ty = spf "Some_%s" (layout_smtty ty)
let mk_none_name ty = spf "None_%s" (layout_smtty ty)

let rec smt_tp_to_sort (env : Dtencoding.z3_env) t =
  let ctx = env.ctx in
  match t with
  (* | Smt_enum { enum_name; enum_elems } -> *)
  (*     get_z3_enum_type ctx (enum_name, enum_elems) *)
  | Smt_Uninterp name -> (
      match Dtencoding.z3_data_type_get env name with
      | Some dt -> dt.sort
      | None when Hashtbl.mem Dtencoding.decl_registry name ->
          _die_with [%here]
            (spf
               "registered datatype %s has no built sort in this ctx's \
                datatype_map"
               name)
      | None -> Sort.mk_uninterpreted_s ctx name)
  (* | Smt_Uninterp _ -> Integer.mk_sort ctx *)
  | Smt_Unit -> Enumeration.mk_sort_s ctx z3_unit_name [ z3_tt_name ]
  | Smt_Int -> Integer.mk_sort ctx
  | Smt_Bool -> Boolean.mk_sort ctx
  | Smt_Char -> Seq.mk_char_sort ctx
  | Smt_String -> Seq.mk_string_sort ctx
  | Smt_Float64 -> FloatingPoint.mk_sort_64 ctx
  | Smt_option smtnt ->
      let option_name = layout_smtty t in
      let some_name = mk_some_name smtnt in
      let none_name = mk_none_name smtnt in
      let constructor_none =
        Datatype.mk_constructor_s ctx none_name (mk_recog ctx none_name) [] []
          []
      in
      let constructor_some =
        Datatype.mk_constructor_s ctx some_name (mk_recog ctx some_name)
          [ Symbol.mk_string ctx (spf "get_%s" some_name) ]
          [ Some (smt_tp_to_sort env smtnt) ]
          [ 0 ]
      in
      Datatype.mk_sort_s ctx option_name [ constructor_none; constructor_some ]
  | Smt_tuple l ->
      let tuple_name = layout_smtty t in
      (* let () = *)
      (*   Printf.printf "smtty(%s) -> %s\n" (show_smtty t) (layout_smtty t) *)
      (* in *)
      let n = List.length l in
      let sym = Symbol.mk_string ctx tuple_name in
      let syms = List.init n (fun i -> tuple_field ctx tuple_name i) in
      let l = List.map (smt_tp_to_sort env) l in
      Tuple.mk_sort ctx sym syms l
  | Smt_record fields ->
      let record_name = layout_smtty t in
      let fields = sort_record fields in
      let constructor =
        Datatype.mk_constructor_s ctx
          (spf "_constr%s" record_name)
          (mk_recog ctx record_name)
          (List.map (fun x -> Symbol.mk_string ctx x.x) fields)
          (List.map (fun x -> Some (smt_tp_to_sort env x.ty)) fields)
          (List.init (List.length fields) (fun i -> i))
      in
      Datatype.mk_sort_s ctx record_name [ constructor ]

let int_to_z3 ctx i = mk_numeral_int ctx i (Integer.mk_sort ctx)
let bool_to_z3 ctx b = if b then mk_true ctx else mk_false ctx
let str_to_z3 ctx str = Seq.mk_string ctx str
let char_to_z3 ctx char = Seq.mk_char ctx (Char.code char)

let float_to_z3 (env : Dtencoding.z3_env) float =
  FloatingPoint.mk_numeral_f env.ctx float (smt_tp_to_sort env Smt_Float64)

(* No memo table: Z3 hash-conses sorts within a ctx, so rebuilding one on each call
   returns the same sort for only the FFI cost. A non-ctx-keyed memo (the old one)
   would hand a second ctx the first ctx's sort and raise a cross-ctx mismatch. *)
let tp_to_sort env t = smt_tp_to_sort env (to_smtty t)

(* A registered datatype that hasn't been built into the env's [datatype_map]
   must crash rather than fall through to an uninterpreted sort. *)
let%test "tp_to_sort dies on a registered datatype missing from datatype_map" =
  let saved = Hashtbl.copy Dtencoding.decl_registry in
  Hashtbl.reset Dtencoding.decl_registry;
  Dtencoding.register_decl
    { dt_name = "boxty"; ctors = [ { cname = "box"; fields = [] } ] };
  let ctx = Z3.mk_context [] in
  let env : Dtencoding.z3_env =
    { ctx; datatype_map = Hashtbl.create 1; rec_func_map = Hashtbl.create 1 }
  in
  let raised =
    try
      ignore (tp_to_sort env (Ty_constructor ("boxty", [])));
      false
    with Failure _ -> true
  in
  Hashtbl.reset Dtencoding.decl_registry;
  Hashtbl.iter (Hashtbl.replace Dtencoding.decl_registry) saved;
  raised

let z3func (env : Dtencoding.z3_env) funcname inptps outtp =
  (* let () = Printf.printf "[%s]funcname: %s\n" __FILE__ funcname in *)
  FuncDecl.mk_func_decl env.ctx
    (Symbol.mk_string env.ctx funcname)
    (List.map (tp_to_sort env) inptps)
    (tp_to_sort env outtp)

(* A [define-fun-rec] measure reports [OP_RECURSIVE] and built-in/datatype ops carry their
   own kind, so only [z3func]'s fallback matches [OP_UNINTERPRETED]. *)
let rec has_uninterpreted_app (e : expr) : bool =
  match AST.get_ast_kind (ast_of_expr e) with
  | APP_AST ->
      FuncDecl.get_decl_kind (get_func_decl e) = OP_UNINTERPRETED
      || List.exists has_uninterpreted_app (get_args e)
  | QUANTIFIER_AST ->
      has_uninterpreted_app
        (Quantifier.get_body (Quantifier.quantifier_of_expr e))
  | _ -> false

(* let arrname_arr arrname = arrname ^ "_a" *)
(* let arrname_length arrname = arrname ^ "_length" *)

(* let arrii_to_z3 ctx name = *)
(*   Z3Array.mk_const_s ctx (arrname_arr name) (Integer.mk_sort ctx) *)
(*     (Integer.mk_sort ctx) *)

(* let array_head_ ctx (arrname, idx) = *)
(*   let a_length = Integer.mk_const_s ctx (arrname_length arrname) in *)
(*   [ mk_lt ctx idx a_length; mk_le ctx (int_to_z3 ctx 0) idx ] *)

(* let array_head ctx (arrname, idxname) = *)
(*   let idx = Integer.mk_const_s ctx idxname in *)
(*   array_head_ ctx (arrname, idx) *)

let tpedvar_to_z3 (env : Dtencoding.z3_env) (tp, name) =
  Expr.mk_const_s env.ctx name @@ tp_to_sort env tp

let make_forall ctx qv body =
  if List.length qv == 0 then body
  else
    Quantifier.expr_of_quantifier
      (Quantifier.mk_forall_const ctx qv body (Some 1) [] [] None None)

let make_exists ctx qv body =
  if List.length qv == 0 then body
  else
    Quantifier.expr_of_quantifier
      (Quantifier.mk_exists_const ctx qv body (Some 1) [] [] None None)

let z3expr_to_bool v =
  match Boolean.get_bool_value v with
  | Z3enums.L_TRUE -> true
  | Z3enums.L_FALSE -> false
  | Z3enums.L_UNDEF -> failwith "z3expr_to_bool"

(* type imp_version = V1 | V2 *)

(* let layout_imp_version = function V1 -> "V1" | V2 -> "V2" *)

(* open Zdatatype *)

(* let bound = 4 *)

(* let get_preds_interp model impv = *)
(*   match impv with *)
(*   | V1 -> List.init bound (fun x -> x) *)
(*   | V2 -> ( *)
(*       let funcs = Model.get_func_decls model in *)
(*       let get func = *)
(*         match Model.get_func_interp model func with *)
(*         | None -> raise @@ failwith "never happen" *)
(*         | Some interp -> *)
(*             let bounds = *)
(*               List.fold_left *)
(*                 (fun l e -> *)
(*                   Model.FuncInterp.FuncEntry.( *)
(*                     List.map *)
(*                       (fun bound -> *)
(*                         if Arithmetic.is_int_numeral bound then *)
(*                           int_of_string *)
(*                           @@ Arithmetic.Integer.numeral_to_string bound *)
(*                         else raise @@ failwith "bad bound") *)
(*                       (get_args e)) *)
(*                   @ l) *)
(*                 [] *)
(*                 (Model.FuncInterp.get_entries interp) *)
(*             in *)
(*             let bounds = List.remove_duplicates bounds in *)
(*             (\* let _ = printf "%s\n" (IntList.to_string bounds) in *\) *)
(*             bounds *)
(*       in *)
(*       let bounds = *)
(*         List.remove_duplicates @@ List.flatten @@ List.map get funcs *)
(*       in *)
(*       match IntList.max_opt bounds with *)
(*       | None -> [ 0 ] *)
(*       | Some ma -> (ma + 1) :: bounds) *)

(* let neg_avoid_timeout_constraint ctx vars body = *)
(*   if List.length vars == 0 then body *)
(*   else *)
(*     let vars = List.map (tpedvar_to_z3 ctx) vars in *)
(*     let is = List.init bound (fun i -> Arithmetic.Integer.mk_numeral_i ctx i) in *)
(*     let ps = *)
(*       List.map *)
(*         (fun x -> *)
(*           Boolean.mk_or ctx (List.map (fun i -> Boolean.mk_eq ctx x i) is)) *)
(*         vars *)
(*     in *)
(*     Boolean.mk_and ctx [ Boolean.mk_and ctx ps; body ] *)

(* let avoid_timeout_constraint ctx fv body = *)
(*   let is = List.init bound (fun i -> Arithmetic.Integer.mk_numeral_i ctx i) in *)
(*   let ps = *)
(*     List.map *)
(*       (fun x -> *)
(*         Boolean.mk_or ctx (List.map (fun i -> Boolean.mk_eq ctx x i) is)) *)
(*       fv *)
(*   in *)
(*   Boolean.mk_implies ctx (Boolean.mk_and ctx ps) body *)

(* let make_forall ctx forallvars body impv = *)
(*   let body = *)
(*     match impv with *)
(*     | V1 -> avoid_timeout_constraint ctx forallvars body *)
(*     | V2 -> body *)
(*   in *)
(*   if List.length forallvars == 0 then body *)
(*   else *)
(*     Quantifier.expr_of_quantifier *)
(*       (Quantifier.mk_forall_const ctx forallvars body (Some 1) [] [] None None) *)

(* let make_exists ctx forallvars body = *)
(*   if List.length forallvars == 0 then body *)
(*   else *)
(*     Quantifier.expr_of_quantifier *)
(*       (Quantifier.mk_exists_const ctx forallvars body (Some 1) [] [] None None) *)

(* let quanti_head ctx forallvars existsvars body = *)
(*   let p = *)
(*     if List.length existsvars == 0 then body *)
(*     else *)
(*       Quantifier.expr_of_quantifier *)
(*         (Quantifier.mk_exists_const ctx existsvars body (Some 1) [] [] None None) *)
(*   in *)
(*   if List.length forallvars == 0 then p *)
(*   else *)
(*     Quantifier.expr_of_quantifier *)
(*       (Quantifier.mk_forall_const ctx forallvars p (Some 1) [] [] None None) *)

(* let encode_ds_var ctx sort_name var_name = *)
(*   let sort = Sort.mk_uninterpreted ctx (Symbol.mk_string ctx sort_name) in *)
(*   let value_func_name = Symbol.mk_string ctx (sort_name ^ "_value") in *)
(*   let value_func = *)
(*     FuncDecl.mk_func_decl ctx value_func_name *)
(*       [ Z3.Arithmetic.Integer.mk_sort ctx ] *)
(*       sort *)
(*   in *)
(*   let index = Integer.mk_const_s ctx var_name in *)
(*   Z3.FuncDecl.apply value_func [ index ] *)
