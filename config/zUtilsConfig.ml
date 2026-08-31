type options = {
  show_var_type_in_prop : bool; [@default false]
  instantiate_poly_type_var_in_smt : bool; [@default false]
  show_record_type_fields : bool; [@default false]
  if_sort_record : bool; [@default true]
  show_var_type_in_term : bool; [@default true]
  show_var_type_in_lit : bool; [@default false]
  show_type_infer_pre_judgement : bool; [@default false]
  show_type_infer_constant_judgement : bool; [@default false]
  show_type_infer_variable_judgement : bool; [@default false]
}
[@@deriving of_yojson { strict = true }]

(* SMT encoding for method predicates. [Axiom] keeps the quantified
   method-predicate axioms and solves on those; [Both] additionally races a
   recursive [define-fun-rec] encoding against them in the subprocess
   portfolio. [Both] requires the program to define recursive [let rec]
   measures for that encoding to race against. *)
type smt_encoding = Axiom | Both [@@deriving of_yojson]

type t = {
  max_printing_size : int; [@default 300]
  log_tags : string list; [@default []]
  prover_timeout_bound : int; [@default 1999]
  options : options; [@default Result.get_ok (options_of_yojson (`Assoc []))]
  pred_extension_rules : (string * string list) list; [@default []]
  smt_encoding : smt_encoding; [@default Axiom]
}
[@@deriving of_yojson { strict = true }]

include ConfigSection.Make (struct
  type nonrec t = t

  let name = "zutils"
  let of_yojson = of_yojson
end)

let get_max_printing_size () = (get ()).max_printing_size
let get_log_tags () = (get ()).log_tags
let get_prover_timeout_bound () = (get ()).prover_timeout_bound
let get_pred_extension_rules () = (get ()).pred_extension_rules
let get_smt_encoding () = (get ()).smt_encoding
let get_show_var_type_in_prop () = (get ()).options.show_var_type_in_prop

let get_instantiate_poly_type_var_in_smt () =
  (get ()).options.instantiate_poly_type_var_in_smt

let get_show_record_type_fields () = (get ()).options.show_record_type_fields
let get_if_sort_record () = (get ()).options.if_sort_record
let get_show_var_type_in_term () = (get ()).options.show_var_type_in_term
let get_show_var_type_in_lit () = (get ()).options.show_var_type_in_lit

let get_show_type_infer_pre_judgement () =
  (get ()).options.show_type_infer_pre_judgement

let get_show_type_infer_constant_judgement () =
  (get ()).options.show_type_infer_constant_judgement

let get_show_type_infer_variable_judgement () =
  (get ()).options.show_type_infer_variable_judgement
