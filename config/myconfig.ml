open MyconfigAst

let default_meta_config_path = "meta-config.json"
let meta_config_path = ref default_meta_config_path
let meta_config : meta_config option ref = ref None

let get_meta () =
  match !meta_config with
  | Some config -> config
  | None ->
      let config_json =
        try Yojson.Safe.from_file !meta_config_path
        with e ->
          let () = Printf.printf "Current dir: %s\n" (Sys.getcwd ()) in
          raise e
      in
      let config =
        match meta_config_of_yojson config_json with
        | Error str ->
            Printf.printf "Meta Config Parsing Error:\n\t%s\n" str;
            failwith "die"
        | Ok c -> normalize_config c
      in
      let () = meta_config := Some config in
      config

let get_mode () = (get_meta ()).mode
let get_max_printing_size () = (get_meta ()).max_printing_size
let get_log_tags () = (get_meta ()).log_tags
let get_bool_option name = get_bool_option_by_name (get_meta ()) name
let get_prover_timeout_bound () = (get_meta ()).prover_timeout_bound
let get_show_var_type_in_prop () = get_bool_option show_var_type_in_prop

let get_instantiate_poly_type_var_in_smt () =
  get_bool_option instantiate_poly_type_var_in_smt

let get_show_record_type_fields () = get_bool_option show_record_type_fields
let get_if_sort_record () = get_bool_option if_sort_record
let get_show_var_type_in_term () = get_bool_option show_var_type_in_term
let get_show_var_type_in_lit () = get_bool_option show_var_type_in_lit

let get_show_type_infer_pre_judgement () =
  get_bool_option show_type_infer_pre_judgement

let get_show_type_infer_constant_judgement () =
  get_bool_option show_type_infer_constant_judgement

let get_show_type_infer_variable_judgement () =
  get_bool_option show_type_infer_variable_judgement

let _log kw (f : unit -> unit) =
  match get_log_tags () with
  | l when List.exists (String.equal kw) l -> f ()
  | _ -> ()

let _log_preprocess = _log "preprocess"
let _log_result = _log "result"
let _log_typing = _log "typing"
let _log_queries = _log "queries"
let _log_minterms = _log "minterms"
let _log_solving = _log "solving"
let _log_stat = _log "stat"
let _log_info = _log "info"
let _log_debug = _log "debug"
let get_prim_path () = (get_meta ()).prim_path
let get_uninterops () = (get_meta ()).abd_templates
let get_name_to_avoid () = (get_meta ()).name_to_avoid
let get_pred_extension_rules () = (get_meta ()).pred_extension_rules

let get_lean_preamble_path () =
  match (get_meta ()).prim_path.lean_preamble with
  | Some p -> p
  | None ->
      failwith
        "meta-config is missing required key 'prim_path.lean_preamble' \
         (needed to dump Lean subtyping queries). Add it to your \
         meta-config.json, pointing at one of \
         data/predefined/lean_preamble_ilist.lean, \
         data/predefined/lean_preamble_rbtree.lean, or \
         data/predefined/lean_preamble_itree.lean (path is resolved \
         relative to the cobb invocation's cwd)."
let global_counter = ref 0
let global_counterpp () = global_counter := !global_counter + 1
