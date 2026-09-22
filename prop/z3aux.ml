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

let rec smt_tp_to_sort (env : Z3decls.z3_env) t =
  let ctx = env.ctx in
  match t with
  | Smt_Uninterp name -> (
      match Hashtbl.find_opt env.datatype_sorts name with
      | Some sort -> sort
      | None when Z3decls.is_registered name ->
          _die_with [%here]
            (spf "registered datatype %s has no sort built in this ctx" name)
      | None -> Sort.mk_uninterpreted_s ctx name)
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

let float_to_z3 (env : Z3decls.z3_env) float =
  FloatingPoint.mk_numeral_f env.ctx float (smt_tp_to_sort env Smt_Float64)

let char_to_z3 ctx char = Seq.mk_char ctx (Char.code char)
let str_to_z3 ctx str = Seq.mk_string ctx str
let tp_to_sort env t = smt_tp_to_sort env (to_smtty t)

let z3func (env : Z3decls.z3_env) funcname inptps outtp =
  FuncDecl.mk_func_decl env.ctx
    (Symbol.mk_string env.ctx funcname)
    (List.map (tp_to_sort env) inptps)
    (tp_to_sort env outtp)

(* Whether [e] applies a symbol the encoder left uninterpreted. Only [z3func]'s
   declarations are [OP_UNINTERPRETED]: a datatype's constructors, recognizers
   and accessors carry their own kinds, and a define-fun-rec is [OP_RECURSIVE]. *)
let rec has_uninterpreted_app (e : expr) : bool =
  match AST.get_ast_kind (ast_of_expr e) with
  | APP_AST ->
      FuncDecl.get_decl_kind (get_func_decl e) = OP_UNINTERPRETED
      || List.exists has_uninterpreted_app (get_args e)
  | QUANTIFIER_AST ->
      has_uninterpreted_app
        (Quantifier.get_body (Quantifier.quantifier_of_expr e))
  | _ -> false

let tpedvar_to_z3 (env : Z3decls.z3_env) (tp, name) =
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

open Z3decls

(* A field of the datatype's own type is a forward reference to the sort being
   built, which Z3 spells as a [None] sort with sort_ref 0. *)
let build_constructor (env : z3_env) (decl : datatype_decl) (ctor : ctor_spec) =
  let ctx = env.ctx in
  let field_sort f =
    match f.ftype with
    | Ty_constructor (n, []) when n = decl.dt_name -> None
    | ty -> Some (tp_to_sort env ty)
  in
  Datatype.mk_constructor_s ctx ctor.cname
    (Symbol.mk_string ctx (recognizer_name ctor.cname))
    (List.map (fun f -> Symbol.mk_string ctx f.fname) ctor.fields)
    (List.map field_sort ctor.fields)
    (List.map (fun _ -> 0) ctor.fields)

(* Z3 hands back the constructor, recognizer and accessor decls in declaration
   order; each is registered under the name the source gave it. *)
let register_sort (env : z3_env) (decl : datatype_decl) : unit =
  let sort =
    Datatype.mk_sort_s env.ctx decl.dt_name
      (List.map (build_constructor env decl) decl.ctors)
  in
  Hashtbl.add env.datatype_sorts decl.dt_name sort;
  List.iter2
    (fun c fd -> register_func env c.cname fd)
    decl.ctors
    (Datatype.get_constructors sort);
  List.iter2
    (fun c fd -> register_func env (recognizer_name c.cname) fd)
    decl.ctors
    (Datatype.get_recognizers sort);
  List.iter2
    (fun c fds ->
      List.iter2 (fun f fd -> register_func env f.fname fd) c.fields fds)
    decl.ctors
    (Datatype.get_accessors sort)

let mk_env ctx : z3_env =
  let env =
    { ctx; datatype_sorts = Hashtbl.create 5; funcs = Hashtbl.create 5 }
  in
  List.iter (register_sort env) (registered_decls ());
  env

(* The facts an uninterpreted sort could not give. *)
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

    let env = mk_env ctx

    let%test "a list datatype encodes as a recursive sort" =
      let apply name args =
        match func_lookup env name with
        | Some fd -> FuncDecl.apply fd args
        | None -> _die_with [%here] (spf "%s is not registered" name)
      in
      let l = Expr.mk_const_s ctx "l" (tp_to_sort env ilist) in
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
