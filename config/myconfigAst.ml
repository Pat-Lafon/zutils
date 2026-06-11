type mode = Debug | Release

(* Accepts both jfp-shape [`List [`String "Debug"]] and HEAD-shape [`String
   "debug"]. Hand-rolled to span both meta-config populations during the port. *)
let mode_of_yojson = function
  | `List [ `String "Debug" ] | `String "debug" -> Ok Debug
  | `List [ `String "Release" ] | `String "release" -> Ok Release
  | other ->
      Error
        (Printf.sprintf
           "mode_of_yojson: expected \"debug\"/\"release\" or \
            [\"Debug\"]/[\"Release\"], got %s"
           (Yojson.Safe.to_string other))

let mode_to_yojson = function
  | Debug -> `String "debug"
  | Release -> `String "release"

type preload_path = {
  predefined_path : string; [@default ""]
  axioms_path : string; [@default ""]
  templates_path : string; [@default ""]
  p_header_template_path : string; [@default ""]
  p_client_template_path : string; [@default ""]
  lean_preamble : string option; [@default None]
  data_type_decls : string option; [@default None]
  normal_typing : string option; [@default None]
  coverage_typing : string option; [@default None]
  axioms : string option; [@default None]
  templates : string option; [@default None]
}
[@@deriving yojson { strict = false }]

type meta_config = {
  log_tags : string list; [@default []]
  mode : mode; [@default Debug]
  max_printing_size : int; [@default 300]
  prim_path : preload_path;
  prover_timeout_bound : int; [@default 1999]
  bool_options : (string * bool) list; [@default []]
  abd_templates : string list; [@default []]
  (* TODO: I found this hack while porting the abduction algorithm over... Ideally we will just be able to remove it but I'll keep it in for now *)
  name_to_avoid : string list; [@default [ "inv"; "mx"; "lo"; "hi" ]]
  (* TODO: Predicate extensions are a hack in general to help support filtering... Maybe we can come up with something more principled *)
  pred_extension_rules : (string * string list) list; [@default []]
}
[@@deriving yojson { strict = false }]

let normalize_config c =
  match c.mode with Release -> { c with log_tags = [] } | Debug -> c

let show_var_type_in_prop = "show_var_type_in_prop"
let instantiate_poly_type_var_in_smt = "instantiate_poly_type_var_in_smt"
let show_record_type_fields = "show_record_type_fields"
let if_sort_record = "if_sort_record"
let show_var_type_in_term = "show_var_type_in_term"
let show_var_type_in_lit = "show_var_type_in_lit"
let show_type_infer_pre_judgement = "show_type_infer_pre_judgement"
let show_type_infer_constant_judgement = "show_type_infer_constant_judgement"
let show_type_infer_variable_judgement = "show_type_infer_variable_judgement"

let default_bool_options =
  [
    (show_var_type_in_prop, false);
    (instantiate_poly_type_var_in_smt, false);
    (show_record_type_fields, false);
    (if_sort_record, true);
    (show_var_type_in_term, true);
    (show_var_type_in_lit, false);
    (show_type_infer_pre_judgement, false);
    (show_type_infer_constant_judgement, false);
    (show_type_infer_variable_judgement, false);
  ]

let get_bool_option_by_name c name =
  match List.assoc_opt name c.bool_options with
  | Some b -> b
  | None -> (
      match List.assoc_opt name default_bool_options with
      | Some b -> b
      | None -> failwith (Printf.sprintf "cannot find option %s" name))
