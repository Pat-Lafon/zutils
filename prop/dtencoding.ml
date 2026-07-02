open Sugar
open Normalty

type z3_data_type = {
  sort : Z3.Sort.sort;
  constructors : (string * Z3.FuncDecl.func_decl) list;
  recognizers : (string * Z3.FuncDecl.func_decl) list;
  accessors : (string * Z3.FuncDecl.func_decl) list;
}

(* A Z3 ctx bundled with the decl maps whose entries are only valid against it:
   applying a decl built in one ctx against another is a Z3 error, so the ctx and
   its maps travel as one value. *)
type z3_env = {
  ctx : Z3.context;
  datatype_map : (string, z3_data_type) Hashtbl.t;
  rec_func_map : (string, Z3.FuncDecl.func_decl) Hashtbl.t;
}

let z3_data_type_get (env : z3_env) (s : string) : z3_data_type option =
  Hashtbl.find_opt env.datatype_map s

let z3_data_type_func_get (dt : z3_data_type) (f : string) :
    Z3.FuncDecl.func_decl option =
  match List.assoc_opt f dt.constructors with
  | Some _ as r -> r
  | None -> (
      match List.assoc_opt f dt.recognizers with
      | Some _ as r -> r
      | None -> List.assoc_opt f dt.accessors)

let z3_data_type_func_lookup (env : z3_env) (dt_name : string) (f : string) :
    Z3.FuncDecl.func_decl option =
  Option.bind (z3_data_type_get env dt_name) (fun dt ->
      z3_data_type_func_get dt f)

(* OCaml-side declaration registry. Populated at config-load by walking
   [data_type_decls.ml] items; consumed at Z3 ctx creation by
   [register_all_for_ctx]. Decoupled so decls survive across Z3 ctx churn. *)
type field_spec = { fname : string; ftype : nt }
type ctor_spec = { cname : string; fields : field_spec list }
type datatype_decl = { dt_name : string; ctors : ctor_spec list }

let decl_registry : (string, datatype_decl) Hashtbl.t = Hashtbl.create 5

let register_decl (d : datatype_decl) : unit =
  let all_fields =
    List.concat_map (fun c -> List.map (fun f -> f.fname) c.fields) d.ctors
  in
  if
    List.length all_fields
    <> List.length (List.sort_uniq String.compare all_fields)
  then
    failwith
      (Printf.sprintf
         "datatype %s has constructors sharing a field name; the functional \
          encoding projects match arms by bare field name and would route \
          through the wrong constructor"
         d.dt_name);
  let cnames = List.map (fun c -> c.cname) d.ctors in
  if List.length cnames <> List.length (List.sort_uniq String.compare cnames)
  then
    failwith
      (Printf.sprintf
         "datatype %s has constructors that collapse to the same name; \
          register_all_for_ctx emits one Z3 constructor per cname and would \
          merge them"
         d.dt_name);
  Hashtbl.replace decl_registry d.dt_name d

let is_dt_accessor (opname : string) : bool =
  Hashtbl.fold
    (fun _ decl acc ->
      acc
      || List.exists
           (fun ctor -> List.exists (fun f -> f.fname = opname) ctor.fields)
           decl.ctors)
    decl_registry false

(* Edges for [topo_sort_decls]: the *other* registered datatypes [d]'s fields
   reference. *)
let external_dt_refs (d : datatype_decl) : string list =
  List.concat_map
    (fun c ->
      List.filter_map
        (fun f ->
          match f.ftype with
          | Ty_constructor (n, [])
            when n <> d.dt_name && Hashtbl.mem decl_registry n ->
              Some n
          | _ -> None)
        c.fields)
    d.ctors
  |> List.sort_uniq String.compare

(* Topological order over [decl_registry] by cross-datatype references: a datatype
   must come before the ones referencing it, so the Lean/Coq export paths emit it
   first and [register_all_for_ctx] builds its sort first. *)
let topo_sort_decls () : datatype_decl list =
  let all = Hashtbl.fold (fun _ d acc -> d :: acc) decl_registry [] in
  let rec loop done_names acc remaining =
    match remaining with
    | [] -> List.rev acc
    | _ -> (
        let ready, blocked =
          List.partition
            (fun d ->
              List.for_all (fun r -> List.mem r done_names) (external_dt_refs d))
            remaining
        in
        match ready with
        | [] ->
            _die_with [%here]
              (Printf.sprintf
                 "Dtencoding: mutually recursive datatypes not supported: %s"
                 (String.concat ", " (List.map (fun d -> d.dt_name) blocked)))
        | _ ->
            let new_done = List.map (fun d -> d.dt_name) ready @ done_names in
            loop new_done (List.rev_append ready acc) blocked)
  in
  loop [] [] all

(* Z3 returns each [func_decl] in the order its constructor (and that
   constructor's fields) were handed to [mk_sorts_s] — i.e. [ctors] order — so a
   positional [combine] re-attaches the names. *)
let extract_z3_data_type sort (ctors : ctor_spec list) : z3_data_type =
  let constructors =
    List.combine
      (List.map (fun c -> c.cname) ctors)
      (Z3.Datatype.get_constructors sort)
  in
  let recognizers =
    List.combine
      (List.map (fun c -> "is_" ^ c.cname) ctors)
      (Z3.Datatype.get_recognizers sort)
  in
  let accessors =
    List.combine
      (List.map (fun c -> List.map (fun f -> f.fname) c.fields) ctors)
      (Z3.Datatype.get_accessors sort)
    |> List.concat_map (fun (fnames, accs) -> List.combine fnames accs)
  in
  { sort; constructors; recognizers; accessors }

(* In the self-ref branch [(None, 0)] is Z3's forward reference: [None] = no prebuilt
   sort, sort_ref [0] = the lone sort [mk_sort_s] is building. [tp_to_sort] is a
   parameter because its home [Z3aux] depends on this module. *)
let register_all_for_ctx ctx (tp_to_sort : z3_env -> nt -> Z3.Sort.sort) :
    z3_env =
  let env =
    { ctx; datatype_map = Hashtbl.create 5; rec_func_map = Hashtbl.create 5 }
  in
  let build_one decl =
    let build_constructor ctor =
      let field_names =
        List.map (fun f -> Z3.Symbol.mk_string ctx f.fname) ctor.fields
      in
      let sorts, sort_refs =
        List.map
          (fun f ->
            match f.ftype with
            | Ty_constructor (n, []) when n = decl.dt_name -> (None, 0)
            | ty -> (Some (tp_to_sort env ty), 0))
          ctor.fields
        |> List.split
      in
      Z3.Datatype.mk_constructor_s ctx ctor.cname
        (Z3.Symbol.mk_string ctx ("is_" ^ ctor.cname))
        field_names sorts sort_refs
    in
    let sort =
      Z3.Datatype.mk_sort_s ctx decl.dt_name
        (List.map build_constructor decl.ctors)
    in
    Hashtbl.replace env.datatype_map decl.dt_name
      (extract_z3_data_type sort decl.ctors)
  in
  List.iter build_one (topo_sort_decls ());
  env
