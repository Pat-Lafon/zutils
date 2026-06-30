open Z3
open Z3aux
open Syntax
open Sugar
open ZUtilsConfig
open Constencoding

let _log = _log "z3encode"

(* The fixed-name [AAppOp] arms below that get a real (constrained) Z3 encoding rather than the
   uninterpreted [z3func] fallback. Keep in sync with those arms. *)
let interpreted_lit_op = function
  | "==" | "!=" | "<=" | ">=" | "<" | ">" | "+" | "-" | "mod" | "*" | "/" | "^"
  | "char_is_digit" | "char_to_int" | "char_le" | "None" | "Some" ->
      true
  | _ -> false

let rec typed_lit_to_z3 (env : Dtencoding.z3_env) lit =
  let ctx = env.ctx in
  let () =
    _log @@ fun () ->
    Printf.printf "lit encoding: %s : %s\n" (Front.layout_lit lit.x)
      (Nt.layout lit.ty)
  in
  match lit.x with
  | ATu lits ->
      Z3.FuncDecl.apply
        (Tuple.get_mk_decl (tp_to_sort env lit.ty))
        (List.map (typed_lit_to_z3 env) lits)
  | AProj (lit, n) ->
      let () =
        _log @@ fun () ->
        Printf.printf "lit encoding: AProj : %s\n" (Nt.layout lit.ty)
      in
      Z3.FuncDecl.apply
        (List.nth (Tuple.get_field_decls (tp_to_sort env lit.ty)) n)
        [ typed_lit_to_z3 env lit ]
  | ARecord _ ->
      let constructor =
        List.nth (Datatype.get_constructors (tp_to_sort env lit.ty)) 0
      in
      let args = as_lit_record [%here] lit.x in
      Z3.FuncDecl.apply constructor
        (List.map (fun (_, x) -> typed_lit_to_z3 env x) args)
  | AField (lit, n) ->
      let accessors =
        List.nth (Datatype.get_accessors (tp_to_sort env lit.ty)) 0
      in
      let idx = Nt.get_field_idx [%here] lit.ty n in
      Z3.FuncDecl.apply (List.nth accessors idx) [ typed_lit_to_z3 env lit ]
  | AC c -> constant_to_z3 env c
  | AVar x -> tpedvar_to_z3 env (x.ty, x.x)
  | AAppOp (op, args) -> (
      let () =
        _log @@ fun () ->
        Pp.printf "app (%s:%s) on %s\n" op.x (Nt.layout op.ty)
          (Zdatatype.List.split_by_comma
             (fun l -> spf "%s:%s" (Front.layout_lit l.x) (Nt.layout l.ty))
             args)
      in
      let args = List.map (typed_lit_to_z3 env) args in
      let () =
        _log @@ fun () ->
        Pp.printf "app (%s:%s) on %s\n" op.x (Nt.layout op.ty)
          (Zdatatype.List.split_by_comma Expr.to_string args)
      in
      match (op.x, args) with
      | "None", [] ->
          let constructor =
            List.nth (Datatype.get_constructors (tp_to_sort env lit.ty)) 0
          in
          Z3.FuncDecl.apply constructor []
      | "Some", [ a ] ->
          let constructor =
            List.nth (Datatype.get_constructors (tp_to_sort env lit.ty)) 1
          in
          Z3.FuncDecl.apply constructor [ a ]
      | "==", [ a; b ] -> Boolean.mk_eq ctx a b
      | "!=", [ a; b ] -> Boolean.mk_not ctx @@ Boolean.mk_eq ctx a b
      | "<=", [ a; b ] -> Arithmetic.mk_le ctx a b
      | ">=", [ a; b ] -> Arithmetic.mk_ge ctx a b
      | "<", [ a; b ] -> Arithmetic.mk_lt ctx a b
      | ">", [ a; b ] -> Arithmetic.mk_gt ctx a b
      | "+", [ a; b ] -> Arithmetic.mk_add ctx [ a; b ]
      | "-", [ a; b ] -> Arithmetic.mk_sub ctx [ a; b ]
      | "mod", [ a; b ] -> Arithmetic.Integer.mk_mod ctx a b
      | "*", [ a; b ] -> Arithmetic.mk_mul ctx [ a; b ]
      | "/", [ a; b ] -> Arithmetic.mk_div ctx a b
      | "^", [ a; b ] -> Arithmetic.mk_power ctx a b
      | "char_is_digit", [ a ] -> Seq.mk_char_is_digit ctx a
      | "char_to_int", [ a ] -> Seq.mk_char_to_int ctx a
      | "char_le", [ a; b ] -> Seq.mk_char_le ctx a b
      | opname, args ->
          let dt_key =
            match Nt.destruct_arr_tp op.ty with
            | t :: _, _ -> Nt.layout t
            | [], _ -> Nt.layout op.ty (* nullary ctor: keyed by return type *)
          in
          let func =
            match Dtencoding.z3_data_type_func_lookup env dt_key opname with
            | Some f -> f
            | None -> (
                (* Method predicate: recursive def while the functional entry is
                   being serialized (the map is populated), else uninterpreted
                   (axiom encoding — the map is empty). *)
                match Func_encoding.lookup env.rec_func_map opname with
                | Some fd -> fd
                | None ->
                    let argsty, retty = Nt.destruct_arr_tp op.ty in
                    z3func env opname argsty retty)
          in
          Z3.FuncDecl.apply func args)
