open Sugar
open Normalty

(* Everything one Z3 context knows by name: the sort built for each registered
   datatype, and every function declaration an encoded term may apply — the
   datatypes' constructors, recognizers and accessors, plus whatever the
   consumer registers on top (a define-fun-rec per method predicate, say). *)
type z3_env = {
  ctx : Z3.context;
  datatype_sorts : (string, Z3.Sort.sort) Hashtbl.t;
  funcs : (string, Z3.FuncDecl.func_decl) Hashtbl.t;
}

let func_lookup (env : z3_env) (name : string) : Z3.FuncDecl.func_decl option =
  Hashtbl.find_opt env.funcs name

let register_func (env : z3_env) (name : string) (fd : Z3.FuncDecl.func_decl) :
    unit =
  if Hashtbl.mem env.funcs name then
    _die_with [%here] (spf "duplicate function symbol %s" name);
  Hashtbl.add env.funcs name fd

type field_spec = { fname : string; ftype : nt }
type ctor_spec = { cname : string; fields : field_spec list }
type datatype_decl = { dt_name : string; ctors : ctor_spec list }

let decl_registry : datatype_decl list ref = ref []

let find_decl (name : string) : datatype_decl option =
  List.find_opt (fun d -> String.equal d.dt_name name) !decl_registry

let is_registered (name : string) : bool = Option.is_some (find_decl name)

(* In source order: [mk_env] needs a field's datatype built before it. *)
let registered_decls () : datatype_decl list = List.rev !decl_registry
let recognizer_prefix = "is_"
let recognizer_name (cname : string) : string = recognizer_prefix ^ cname

(* Every name a declaration claims in the one namespace [funcs] keys on. *)
let names_of (d : datatype_decl) : string list =
  d.dt_name
  :: List.concat_map
       (fun c ->
         c.cname :: recognizer_name c.cname
         :: List.map (fun f -> f.fname) c.fields)
       d.ctors

(* Names are unique across every registered datatype, not just within one: the
   encoder resolves an applied symbol by name alone. *)
let register_decl (d : datatype_decl) : unit =
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

let exists_ctor (p : ctor_spec -> bool) : bool =
  List.exists (fun d -> List.exists p d.ctors) !decl_registry

let is_dt_accessor (opname : string) : bool =
  exists_ctor (fun c ->
      List.exists (fun f -> String.equal f.fname opname) c.fields)

let recognizer_ctor (opname : string) : string option =
  if String.starts_with ~prefix:recognizer_prefix opname then
    let n = String.length recognizer_prefix in
    let cname = String.sub opname n (String.length opname - n) in
    if exists_ctor (fun c -> String.equal c.cname cname) then Some cname
    else None
  else None
