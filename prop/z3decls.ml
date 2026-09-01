open Sugar
open Normalty

type z3_data_type = {
  sort : Z3.Sort.sort;
  constructors : (string * Z3.FuncDecl.func_decl) list;
  recognizers : (string * Z3.FuncDecl.func_decl) list;
  accessors : (string * Z3.FuncDecl.func_decl) list;
}

type z3_env = {
  ctx : Z3.context;
  datatype_map : (string, z3_data_type) Hashtbl.t;
  rec_func_map : (string, Z3.FuncDecl.func_decl) Hashtbl.t;
}

let z3_data_type_get (env : z3_env) (s : string) : z3_data_type option =
  Hashtbl.find_opt env.datatype_map s

let z3_data_type_func_lookup (env : z3_env) (dt_name : string) (f : string) :
    Z3.FuncDecl.func_decl option =
  Option.bind (z3_data_type_get env dt_name) (fun dt ->
      List.find_map (List.assoc_opt f)
        [ dt.constructors; dt.recognizers; dt.accessors ])

let rec_func_lookup (env : z3_env) (name : string) :
    Z3.FuncDecl.func_decl option =
  Hashtbl.find_opt env.rec_func_map name

let register_rec_func (env : z3_env) (name : string)
    (fd : Z3.FuncDecl.func_decl) : unit =
  if Hashtbl.mem env.rec_func_map name then
    _die_with [%here] (spf "duplicate functional symbol %s" name);
  Hashtbl.add env.rec_func_map name fd

type field_spec = { fname : string; ftype : nt }
type ctor_spec = { cname : string; fields : field_spec list }
type datatype_decl = { dt_name : string; ctors : ctor_spec list }

let decl_registry : datatype_decl list ref = ref []

let find_decl (name : string) : datatype_decl option =
  List.find_opt (fun d -> String.equal d.dt_name name) !decl_registry

let is_registered (name : string) : bool = Option.is_some (find_decl name)

(* Registration order is source order, and OCaml requires a datatype be declared
   before it is referenced, so a field's own datatype is always registered first. *)
let registered_decls () : datatype_decl list = List.rev !decl_registry

let rec reject_dup (d : datatype_decl) = function
  | [] -> ()
  | n :: tl when List.exists (String.equal n) tl ->
      _die_with [%here] (spf "datatype %s: duplicate name %s" d.dt_name n)
  | _ :: tl -> reject_dup d tl

let register_decl (d : datatype_decl) : unit =
  if is_registered d.dt_name then
    _die_with [%here] (spf "duplicate datatype %s" d.dt_name);
  reject_dup d
    (List.concat_map (fun c -> List.map (fun f -> f.fname) c.fields) d.ctors);
  reject_dup d (List.map (fun c -> c.cname) d.ctors);
  decl_registry := d :: !decl_registry

let exists_ctor (p : ctor_spec -> bool) : bool =
  List.exists (fun d -> List.exists p d.ctors) !decl_registry

let is_dt_accessor (opname : string) : bool =
  exists_ctor (fun c ->
      List.exists (fun f -> String.equal f.fname opname) c.fields)

let recognizer_prefix = "is_"
let recognizer_name (cname : string) : string = recognizer_prefix ^ cname

let recognizer_ctor (opname : string) : string option =
  if String.starts_with ~prefix:recognizer_prefix opname then
    let n = String.length recognizer_prefix in
    let cname = String.sub opname n (String.length opname - n) in
    if exists_ctor (fun c -> String.equal c.cname cname) then Some cname
    else None
  else None
