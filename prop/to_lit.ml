open Ast
open OcamlParser
open Oparse
open Sugar
open Zdatatype
open Parsetree
open To_id
open To_constant
open Mutils
open Ast_helper

let normal_apply f args =
  Exp.apply f @@ List.map (fun x -> (Asttypes.Nolabel, x)) args

let rec lit_to_expr expr =
  match expr with
  | AC c -> constant_to_expr c
  | AAppOp (op, args) ->
      mk_op_apply
        (lit_to_expr (AVar op.x#:op.ty), List.map typed_lit_to_expr args)
  | ATu l -> Exp.tuple (List.map typed_lit_to_expr l)
  | AProj (lit, 0) -> normal_apply (mkvar fst_func) [ lit_to_expr lit.x ]
  | AProj (lit, 1) -> normal_apply (mkvar snd_func) [ lit_to_expr lit.x ]
  | AProj (lit, n) ->
      normal_apply (mkvar proj_func)
        [ lit_to_expr lit.x; constant_to_expr (I n) ]
  | ARecord l ->
      Exp.record
        (List.map (fun (x, lit) -> (id_to_longid x, lit_to_expr lit.x)) l)
        None
  | AField (lit, fd) -> Exp.field (lit_to_expr lit.x) (id_to_longid fd)
  | AVar x ->
      if ZUtilsConfig.get_show_var_type_in_prop () then
        Exp.constraint_ (mkvar x.x) (Nt.t_to_core_type x.ty)
      else mkvar x.x

and typed_lit_to_expr expr =
  if ZUtilsConfig.get_show_var_type_in_lit () then
    match expr.ty with
    | Nt.Ty_unknown -> lit_to_expr expr.x
    | _ ->
        desc_to_ocamlexpr
        @@ Pexp_constraint (lit_to_expr expr.x, Nt.t_to_core_type expr.ty)
  else lit_to_expr expr.x

let rec layout_lit_to_smtlib2 expr =
  let aux expr =
    match expr with
    | AC c -> To_constant.layout_constant c
    | AAppOp (op, args) ->
        let op = match op.x with "==" -> "=" | _ -> op.x in
        spf "(%s %s)" op (List.split_by " " layout_typed_lit_to_smtlib2 args)
    | ATu args ->
        spf "(%s)" (List.split_by_comma layout_typed_lit_to_smtlib2 args)
    | AProj (lit, n) ->
        spf "(%s %s %i)" proj_func (layout_typed_lit_to_smtlib2 lit) n
    | ARecord args ->
        spf "{%s}"
          (List.split_by ";"
             (fun (x, lit) -> spf "%s = %s" x (layout_typed_lit_to_smtlib2 lit))
             args)
    | AField (lit, n) -> spf "%s.%s" (layout_typed_lit_to_smtlib2 lit) n
    | AVar x -> x.x
  in
  aux expr

and layout_typed_lit_to_smtlib2 expr = layout_lit_to_smtlib2 expr.x

let layout_lit lit = string_of_expression @@ lit_to_expr lit
let layout = layout_lit
let layout_typed_lit lit = layout lit.x

let layout_typed_lit_mp mp lit =
  string_of_expression @@ lit_to_expr (Syntax.map_op mp lit.x)

open Nt

let constructor_const_opt c =
  match c with
  | "true" -> Some (B true)
  | "false" -> Some (B false)
  | "()" -> Some U
  | _ -> None

let rec lit_of_expr expr =
  match expr.pexp_desc with
  | Pexp_tuple es -> ATu (List.map typed_lit_of_expr es)
  | Pexp_record (args, None) ->
      ARecord
        (List.map (fun (x, e) -> (longid_to_id x, typed_lit_of_expr e)) args)
  | Pexp_field (e, fd) -> AField (typed_lit_of_expr e, longid_to_id fd)
  | Pexp_constraint _ -> _die [%here]
  | Pexp_ident id -> AVar (longid_to_id id)#:Ty_unknown
  | Pexp_construct (c, args) -> (
      let args =
        match args with
        | None -> []
        | Some args -> (
            let args = typed_lit_of_expr args in
            match args.x with ATu es -> es | _ -> [ args ])
      in
      let op = longid_to_id c in
      match (constructor_const_opt op, args) with
      | Some c, _ -> AC c
      | _, _ -> AAppOp (op#:Ty_unknown, args))
  | Pexp_constant _ -> AC (expr_to_constant expr)
  | Pexp_let _ -> _die [%here]
  | Pexp_apply (func, args) ->
      let args = List.map (fun x -> typed_lit_of_expr @@ snd x) args in
      let func = typed_lit_of_expr func in
      let res =
        match func.x with
        | AVar f when String.equal f.x fst_func -> (
            match args with [ lit ] -> AProj (lit, 0) | _ -> _die [%here])
        | AVar f when String.equal f.x snd_func -> (
            match args with [ lit ] -> AProj (lit, 1) | _ -> _die [%here])
        | AVar f when String.equal f.x proj_func -> (
            match args with
            | [ lit; { x = AC (I n); _ } ] -> AProj (lit, n)
            | _ -> _die [%here])
        | AVar f ->
            AAppOp (f, args)
            (* match string_to_op_opt f.x with *)
            (* | Some _ -> AAppOp (f, args) *)
            (* | None -> _die [%here] *)
        | _ -> _die [%here]
      in
      res
  | Pexp_ifthenelse _ -> _die [%here]
  | Pexp_match _ -> _die [%here]
  | Pexp_fun _ -> _die [%here]
  | Pexp_sequence _ -> _die [%here]
  | _ ->
      raise
      @@ failwith
           (Sugar.spf "not imp client parsing:%s" @@ string_of_expression expr)

and typed_lit_of_expr expr =
  match expr.pexp_desc with
  | Pexp_constraint (expr, ty) -> (lit_of_expr expr)#:(Nt.core_type_to_t ty)
  | _ -> (lit_of_expr expr)#:Ty_unknown

let of_expr = lit_of_expr
let layout lit = string_of_expression @@ lit_to_expr lit
