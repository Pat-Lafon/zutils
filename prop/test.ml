open Prover
open Syntax
open Myconfig
open Z3

open Sugar
(** Inline test *)

open OcamlParser.Oparse
open To_ctx
open Zdatatype

let _builtin_normal_context = ref None

let _builtin_normal_context_file =
  "/Users/zhezzhou/workspace/CoverageType/data/predefined/basic_typing.ml"

let _builtin_axioms_file =
  "/Users/zhezzhou/workspace/CoverageType/data/predefined/axioms.ml"

let init_for_inline_test (nctx, axioms) =
  let alias, ctx = get_normal_ctx nctx in
  let inline_record (x, args, record_ty) ty =
    let f ts =
      let m = StrMap.of_list @@ _safe_combine [%here] args ts in
      let record_ty = Nt.msubst_nt m record_ty in
      record_ty
    in
    let ty = Nt.subst_constructor_nt (x, f) ty in
    let core =
      match record_ty with
      | Nt.Ty_record { alias; fds } -> (List.map _get_x fds, alias)
      | _ -> _die [%here]
    in
    Nt.subst_alias_in_record_nt core ty
  in
  let inline nt =
    let res = List.fold_right inline_record alias nt in
    (* let () = *)
    (*   _log @@ fun () -> *)
    (*   Printf.printf "decls %s \n" (List.split_by_comma _get_x decls); *)
    (*   Printf.printf "inline %s ==> %s\n" (Nt.layout nt) (Nt.layout res) *)
    (* in *)
    res
  in
  let ctx = Typectx.map_ctx inline ctx in
  let axioms = get_axiom_ctx axioms in
  let axioms =
    List.map (fun (a, b, prop) -> (a, b, map_prop inline prop)) axioms
  in
  let axioms =
    List.map
      (fun (name, tasks, prop) ->
        let () = Printf.printf "%s\n" (Front.layout_prop prop) in
        ( name,
          tasks,
          Typecheck.prop_type_check ctx [ unified_axiom_type_var ] prop ))
      axioms
  in
  let () = update_axioms axioms in
  ctx

let get_normal_context () =
  match !_builtin_normal_context with
  | None ->
      let ctx =
        init_for_inline_test (_builtin_normal_context_file, _builtin_axioms_file)
      in
      _builtin_normal_context := Some ctx;
      ctx
  | Some ctx -> ctx

let handle_prop nctx tvars str =
  let prop = Front.of_expr @@ parse_expression str in
  let prop = Typecheck.prop_type_check nctx tvars prop in
  prop

let handle_prop_from_sexp_file (name, i) =
  let ic =
    In_channel.open_text
      (spf "/Users/zhezzhou/workspace/zutils/data/query_failure/%s_%i.scm" name
         i)
  in
  try
    let str = In_channel.input_all ic in
    let res = prop_of_sexp Nt.nt_of_sexp @@ Sexplib.Sexp.of_string str in
    In_channel.close ic;
    res
  with e -> raise e

(* let%test "test" = *)
(*   let () = *)
(*     meta_config_path := "/Users/zhezzhou/workspace/zutils/meta-config.json" *)
(*   in *)
(*   let nctx = get_normal_context () in *)
(*   let prop = *)
(*     handle_prop nctx [] *)
(*       "fun ((x [@ex]) : int * bool) ((y [@ex]) : bool * int) -> Some (fst x) \ *)
(*        == Some (snd y) && Some (snd x) == None" *)
(*   in *)
(*   let () = Printf.printf "Prop: %s:\n" @@ Front.layout prop in *)
(*   let () = Printf.printf "Prop: %s:\n" @@ show_prop prop in *)
(*   let res = check_sat (None, prop) in *)
(*   let () = Pp.printf "@{<bold>SAT(%s): @}\n" (layout_smt_result res) in *)
(*   false *)

(* let%test "query" = *)
(*   let open Data in *)
(*   let () = *)
(*     meta_config_path := "/Users/zhezzhou/workspace/zutils/meta-config.json" *)
(*   in *)
(*   let prop = prop_of_sexp Nt.nt_of_sexp @@ Sexplib.Sexp.of_string _p6 in *)
(*   let () = Printf.printf "Prop: %s:\n" @@ Front.layout prop in *)
(*   let ax = handle_prop ax_list_mem_has_nth in *)
(*   let () = Printf.printf "Ax: %s:\n" @@ Front.layout ax in *)
(*   let () = update_axioms [ ("ax", [], ax) ] in *)
(*   let res = check_sat (None, prop) in *)
(*   let () = Pp.printf "@{<bold>SAT(%s): @}\n" (layout_smt_result res) in *)
(*   false *)
open Sugar

let analysize_failure model prop =
  let { ctx; _ } = get_prover () in
  let rec aux prop =
    match prop with
    | Lit lit ->
        (* let () = Printf.printf "lit: %s\n" (Front.layout_lit lit.x) in *)
        let lit_z3 = Litencoding.typed_lit_to_z3 ctx lit in
        let res = Z3.Model.eval model lit_z3 false in
        let res_str =
          match res with None -> "none" | Some e -> Expr.to_string e
        in
        let prop =
          match bool_of_string_opt res_str with
          | Some true -> mk_true
          | Some false -> mk_false
          | None -> prop
        in
        (* let () = Printf.printf "%s\n" res_str in *)
        prop
    | Exists { body; qv } -> Exists { body = aux body; qv }
    | Forall { body; qv } -> Forall { body = aux body; qv }
    | And l -> smart_and (List.map aux l)
    | Or l -> smart_or (List.map aux l)
    | Implies (e1, e2) -> smart_implies (aux e1) (aux e2)
    | Iff (e1, e2) -> Iff (aux e1, aux e2)
    | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
    | Not e -> smart_not (aux e)
  in
  let prop' = aux prop in
  let () = Printf.printf "Prop in model:\n%s\n" (Front.layout prop') in
  prop'

let eval_ex_prim_in_prop (task_name, sprop) =
  let { ctx; _ } = get_prover () in
  let rec aux (evars, sprop) =
    let () = Printf.printf "Eval Prop: \n%s\n" (Front.layout sprop) in
    match evars with
    | [] -> sprop
    | qv :: evars when Nt.equal_nt qv.ty Nt.int_ty -> (
        let body = snf_quantified_var_by_name qv.x sprop in
        let () = Printf.printf "Eval SNF Prop: \n%s\n" (Front.layout body) in
        let axioms = select_axioms (Some task_name, body) in
        let res = check_sat ~axioms (Some task_name, body) in
        let () = Pp.printf "@{<bold>SAT(%s): @}\n" (layout_smt_result res) in
        match res with
        | SmtSat model -> (
            let () = Printf.printf "Sat\n" in
            let expr = Litencoding.typed_lit_to_z3 ctx (tvar_to_lit qv) in
            match Model.eval model expr false with
            | None -> sprop
            | Some res -> (
                match int_of_string_opt (Expr.to_string res) with
                | Some i ->
                    let () = Printf.printf "%s := %i\n" qv.x i in
                    let lit = AC (I i) in
                    let body =
                      SimplProp.eval_arithmetic
                      @@ subst_prop_instance qv.x lit body
                    in
                    let _ = analysize_failure model body in
                    aux (evars, body)
                | None -> sprop))
        | _ -> sprop)
    | _ :: evars -> aux (evars, sprop)
  in
  let qvs, _ = lift_ex_quantifiers sprop in
  let sprop = aux (qvs, sprop) in
  let ax = SimplProp.simpl_query @@ to_nnf (smart_not sprop) in
  let () = Printf.printf "Suggested Axiom: \n%s\n" (Front.layout ax) in
  let () = Printf.printf "let[@axiom] tmp = %s\n" (Front.layout_prop__raw ax) in
  ()

(* let ax_list_mem_has_nth = *)
(*   "fun (l : 'c list) (v : 'c) ->\n\ *)
(*   \  (list_mem l v) #==> (fun ((idx [@ex]) : int) ->\n\ *)
(*   \  0 <= idx && idx < list_len l && list_nth_pred l idx v)" *)

(* let list_snd_mem_has_hd_tl = *)
(*  fun (l : (int * 'a) list) (v : 'a) -> *)
(*   (list_snd_mem l v) *)
(*   #==> (fun ((hde [@ex]) : int * 'a) ((tle [@ex]) : (int * 'a) list) -> *)
(*   hd l hde && tl l tle) *)

let list_snd_mem_has_hd_tl =
  " fun (l : (int * 'a) list) (v : 'a) ->\n\
  \  (list_snd_mem l v)\n\
  \  #==> (fun ((hde [@ex]) : int * 'a) ((tle [@ex]) : (int * 'a) list) ->\n\
  \  hd l hde && tl l tle)"

let%test "query_from_file" =
  let () =
    meta_config_path := "/Users/zhezzhou/workspace/zutils/meta-config.json"
  in
  let task_name = "list_repeat" in
  let _ = get_normal_context () in
  let prop = handle_prop_from_sexp_file (task_name, 1) in
  let () = Printf.printf "Prop:\n%s:\n\n" @@ Front.layout prop in
  let sprop = SimplProp.instantiate_quantified_option prop in
  let () = Printf.printf "Simplied Prop:\n%s\n" @@ Front.layout sprop in
  let () =
    Printf.printf "let[@axiom] tmp = %s\n" (Front.layout_prop__raw sprop)
  in
  (* let () = _die [%here] in *)
  let sprop = SimplProp.simpl_query_by_eq prop in
  let () = Printf.printf "Simplied Prop:\n%s\n" @@ Front.layout sprop in
  let sprop = to_nnf @@ SimplProp.instantiate_quantified_bool sprop in
  let () = Printf.printf "Simplied Prop:\n%s\n" @@ Front.layout sprop in
  let axioms = select_axioms (Some task_name, sprop) in
  let res = check_sat ~axioms (Some task_name, sprop) in
  let () = Pp.printf "@{<bold>SAT(%s): @}\n" (layout_smt_result res) in
  let () =
    match res with
    | SmtSat _ -> eval_ex_prim_in_prop (task_name, sprop)
    (* analysize_failure model sprop *)
    | _ -> ()
  in
  false
