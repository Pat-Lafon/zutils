open Prover
open Syntax

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
    res
  in
  let ctx = Typectx.map_ctx inline ctx in
  let axioms = get_axiom_ctx axioms in
  let axioms = List.map (fun (a, prop) -> (a, map_prop inline prop)) axioms in
  let axioms =
    List.map
      (fun (name, prop) ->
        let () = Printf.printf "%s\n" (Front.layout_prop prop) in
        (name, Typecheck.prop_type_check ctx [ unified_axiom_type_var ] prop))
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

let list_snd_mem_has_hd_tl =
  " fun (l : (int * 'a) list) (v : 'a) ->\n\
  \  (list_snd_mem l v)\n\
  \  #==> (fun ((hde [@ex]) : int * 'a) ((tle [@ex]) : (int * 'a) list) ->\n\
  \  hd l hde && tl l tle)"
