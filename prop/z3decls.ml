open Normalty

type field_spec = { fname : string; ftype : nt }
type ctor_spec = { cname : string; fields : field_spec list }
type datatype_decl = { dt_name : string; ctors : ctor_spec list }

let decl_registry : datatype_decl list ref = ref []

let exists_ctor (p : ctor_spec -> bool) : bool =
  List.exists (fun d -> List.exists p d.ctors) !decl_registry

let is_dt_accessor (opname : string) : bool =
  exists_ctor (fun c ->
      List.exists (fun f -> String.equal f.fname opname) c.fields)
