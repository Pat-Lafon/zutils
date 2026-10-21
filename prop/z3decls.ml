open Sugar
open Normalty

(* The datatypes a consumer declares, by source name. Each Z3 context builds its
   own sorts and declarations from them. *)
type field_spec = { fname : string; ftype : nt }
type ctor_spec = { cname : string; fields : field_spec list }
type datatype_decl = { dt_name : string; ctors : ctor_spec list }

let decl_registry = ref []

let find_decl name =
  List.find_opt (fun d -> String.equal d.dt_name name) !decl_registry

let is_registered name = Option.is_some (find_decl name)

(* In source order: a field's datatype is built before the datatype using it. *)
let registered_decls () = List.rev !decl_registry
let recognizer_prefix = "is_"
let recognizer_name cname = recognizer_prefix ^ cname

(* Every name a declaration claims in the one namespace applied symbols resolve
   in. *)
let names_of d =
  List.concat_map
    (fun c ->
      c.cname :: recognizer_name c.cname :: List.map (fun f -> f.fname) c.fields)
    d.ctors

(* Names are unique across every registered datatype, not just within one: the
   encoder resolves an applied symbol by name alone. *)
let register_decl d =
  if is_registered d.dt_name then
    _die_with [%here] (spf "datatype %s is already registered" d.dt_name);
  let taken = List.concat_map names_of !decl_registry in
  let rec reject = function
    | [] -> ()
    | n :: tl ->
        if List.mem n tl || List.mem n taken then
          _die_with [%here]
            (spf "datatype %s: name %s is already taken" d.dt_name n);
        reject tl
  in
  reject (names_of d);
  decl_registry := d :: !decl_registry
