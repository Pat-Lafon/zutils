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
        String.equal name x)
      cs
  in
  Option.map (fun i -> Z3.FuncDecl.apply i []) i

let get_int_by_name m x =
  Option.map
    (fun i ->
      match Z3.Model.eval m i false with
      | None -> _die_with [%here] "get_int"
      | Some v -> int_of_string @@ Z3.Arithmetic.Integer.numeral_to_string v)
    (find_const_in_model m x)

let get_string_by_name m x =
  Option.map
    (fun i ->
      match Z3.Model.eval m i false with
      | None -> _die_with [%here] "get_string"
      | Some v ->
          let str = Expr.to_string v in
          let str = List.of_seq @@ String.to_seq str in
          let str = List.filter (fun c -> not (Char.equal c '"')) str in
          String.of_seq @@ List.to_seq str)
    (find_const_in_model m x)

let tuple_field ctx n i = Symbol.mk_string ctx (spf "%s_%i" n i)

open Zdatatype

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
  if List.length qv = 0 then body
  else
    Quantifier.expr_of_quantifier
      (Quantifier.mk_forall_const ctx qv body (Some 1) [] [] None None)

let make_exists ctx qv body =
  if List.length qv = 0 then body
  else
    Quantifier.expr_of_quantifier
      (Quantifier.mk_exists_const ctx qv body (Some 1) [] [] None None)

let z3expr_to_bool v =
  match Boolean.get_bool_value v with
  | Z3enums.L_TRUE -> true
  | Z3enums.L_FALSE -> false
  | Z3enums.L_UNDEF -> failwith "z3expr_to_bool"

let%test_module "datatype encoding" =
  (module struct
    let ilist = Ty_constructor ("ilist", [])
    let ctx = Z3.mk_context []

    let () =
      ZUtilsConfig.(set (Result.get_ok (of_yojson (`Assoc []))));
      register_decl
        {
          dt_name = "ilist";
          ctors =
            [
              { cname = "nil"; fields = [] };
              {
                cname = "cons";
                fields =
                  [
                    { fname = "head"; ftype = int_ty };
                    { fname = "tail"; ftype = ilist };
                  ];
              };
            ];
        }

    let%test "a list datatype encodes as a recursive sort" =
      let apply name args =
        match func_lookup ctx name with
        | Some fd -> FuncDecl.apply fd args
        | None -> _die_with [%here] (spf "%s is not registered" name)
      in
      let l = Expr.mk_const_s ctx "l" (tp_to_sort ctx ilist) in
      let cell = apply "cons" [ int_to_z3 ctx 1; l ] in
      let entails e =
        let solver = Z3.Solver.mk_solver ctx None in
        Z3.Solver.add solver [ mk_not ctx e ];
        Z3.Solver.check solver [] = Z3.Solver.UNSATISFIABLE
      in
      entails (apply "is_cons" [ cell ])
      && entails (mk_eq ctx (apply "head" [ cell ]) (int_to_z3 ctx 1))
      && entails (mk_eq ctx (apply "tail" [ cell ]) l)
      && entails (mk_not ctx (mk_eq ctx cell l))
  end)
