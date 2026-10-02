open Sugar
open Normalty

(* Everything one Z3 context knows by name: the sort built for each registered
   datatype, and every function declaration registered by name — the
   datatypes' constructors, recognizers and accessors, plus whatever the
   consumer registers on top (a define-fun-rec per method predicate, say). *)
type z3_env = {
  ctx : Z3.context;
  datatype_sorts : (string, Z3.Sort.sort) Hashtbl.t;
  funcs : (string, Z3.FuncDecl.func_decl) Hashtbl.t;
}

let func_lookup env name = Hashtbl.find_opt env.funcs name

let register_func env name fd =
  if Hashtbl.mem env.funcs name then
    _die_with [%here] (spf "duplicate function symbol %s" name);
  Hashtbl.add env.funcs name fd

type field_spec = { fname : string; ftype : nt }
type ctor_spec = { cname : string; fields : field_spec list }
type datatype_decl = { dt_name : string; ctors : ctor_spec list }

let decl_registry = ref []

let find_decl name =
  List.find_opt (fun d -> String.equal d.dt_name name) !decl_registry

let is_registered name = Option.is_some (find_decl name)

(* In source order: [mk_env] needs a field's datatype built before it. *)
let registered_decls () = List.rev !decl_registry
let recognizer_prefix = "is_"
let recognizer_name cname = recognizer_prefix ^ cname

(* Every name a declaration claims in the one namespace [funcs] keys on. *)
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

let exists_ctor p = List.exists (fun d -> List.exists p d.ctors) !decl_registry

let is_dt_accessor opname =
  exists_ctor (fun c ->
      List.exists (fun f -> String.equal f.fname opname) c.fields)

let recognizer_ctor opname =
  if String.starts_with ~prefix:recognizer_prefix opname then
    let n = String.length recognizer_prefix in
    let cname = String.sub opname n (String.length opname - n) in
    if exists_ctor (fun c -> String.equal c.cname cname) then Some cname
    else None
  else None
