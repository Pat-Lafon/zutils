open Sugar
open Normalty

type z3_data_type = {
  sort : Z3.Sort.sort;
  constructors : (string * Z3.FuncDecl.func_decl) list;
  recognizers : (string * Z3.FuncDecl.func_decl) list;
  accessors : (string * Z3.FuncDecl.func_decl) list;
}

let datatype_map : (string, z3_data_type) Hashtbl.t = Hashtbl.create 5

let z3_data_type_get (s : string) : z3_data_type option =
  Hashtbl.find_opt datatype_map s

let z3_data_type_func_get (dt : z3_data_type) (f : string) :
    Z3.FuncDecl.func_decl option =
  match List.assoc_opt f dt.constructors with
  | Some _ as r -> r
  | None -> (
      match List.assoc_opt f dt.recognizers with
      | Some _ as r -> r
      | None -> List.assoc_opt f dt.accessors)

let z3_data_type_func_lookup (dt_name : string) (f : string) :
    Z3.FuncDecl.func_decl option =
  Option.bind (z3_data_type_get dt_name) (fun dt -> z3_data_type_func_get dt f)

(* Constructor case fed to [create_data_type]: [(name, [(field_name, field_sort_or_self_ref)])].
   [None] in the sort slot is the Z3 marker for "this datatype" (self-recursive field). *)
type case = string * (string * Z3.Sort.sort option) list

let create_constructor ctx (case : case) =
  let name, args = case in
  let symbols, types =
    List.map (fun (s, t) -> (Z3.Symbol.mk_string ctx s, t)) args |> List.split
  in
  let zeros = List.map (fun _ -> 0) types in
  let recognizer = Z3.Symbol.mk_string ctx ("is_" ^ name) in
  Z3.Datatype.mk_constructor_s ctx name recognizer symbols types zeros

let create_data_type ctx name (cases : case list) =
  let init_constructors = List.map (create_constructor ctx) cases in
  let sort = Z3.Datatype.mk_sort_s ctx name init_constructors in
  let dt_constructors = Z3.Datatype.get_constructors sort in
  let constructor_names = List.map fst cases in
  let constructors = List.combine constructor_names dt_constructors in
  let recognizers =
    List.combine
      (List.map (fun c -> "is_" ^ c) constructor_names)
      (Z3.Datatype.get_recognizers sort)
  in
  let accessors =
    List.combine cases (Z3.Datatype.get_accessors sort)
    |> List.map (fun (a, b) -> List.combine (snd a |> List.map fst) b)
    |> List.flatten
  in
  { sort; constructors; recognizers; accessors }

(* OCaml-side declaration registry. Populated at config-load by walking
   [data_type_decls.ml] items; consumed at Z3 ctx creation by
   [register_all_for_ctx]. Decoupled so decls survive across Z3 ctx churn. *)
type field_spec = { fname : string; ftype : nt }
type ctor_spec = { cname : string; fields : field_spec list }
type datatype_decl = { dt_name : string; ctors : ctor_spec list }

let decl_registry : (string, datatype_decl) Hashtbl.t = Hashtbl.create 5

let register_decl (d : datatype_decl) : unit =
  Hashtbl.replace decl_registry d.dt_name d

(* True iff [opname] is the field name of some constructor of some registered
   datatype (i.e. a datatype accessor like [head]/[tail]/[left]/[color]/...).
   Used by [SimplProp.simpl_query_by_eq] to refuse inlining existentials whose
   defining equation is an accessor application: the Lean dump path needs the
   bridging existential so Lean's [Some] coercion can reconcile its Option-
   wrapped accessor types with Cobb's raw view. *)
let is_dt_accessor (opname : string) : bool =
  Hashtbl.fold
    (fun _ decl acc ->
      acc
      || List.exists
           (fun ctor ->
             List.exists (fun f -> f.fname = opname) ctor.fields)
           decl.ctors)
    decl_registry false

(* External references to *other registered datatypes*. Builtin types
   (int/bool/...) don't gate ordering — they go straight through [tp_to_sort]. *)
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

(* Topological order over [decl_registry] by cross-datatype references.
   Self-references are fine (encoded as [None] inside [register_all_for_ctx]).
   Mutual recursion across two registered datatypes hits the [_die] path —
   Z3's [mk_sorts_s] would be required to support it; no current benchmark
   needs it. *)
let topo_sort_decls () : datatype_decl list =
  let all = Hashtbl.fold (fun _ d acc -> d :: acc) decl_registry [] in
  let rec loop done_names acc remaining =
    match remaining with
    | [] -> List.rev acc
    | _ -> (
        let ready, blocked =
          List.partition
            (fun d ->
              List.for_all
                (fun r -> List.mem r done_names)
                (external_dt_refs d))
            remaining
        in
        match ready with
        | [] ->
            _die_with [%here]
              (Printf.sprintf
                 "Dtencoding: mutually recursive datatypes not supported: %s"
                 (String.concat ", "
                    (List.map (fun d -> d.dt_name) blocked)))
        | _ ->
            let new_done = List.map (fun d -> d.dt_name) ready @ done_names in
            loop new_done (List.rev_append ready acc) blocked)
  in
  loop [] [] all

(* Build Z3 sorts for every registered decl against [ctx] and stash them in
   [datatype_map]. Caller supplies [tp_to_sort] to break the cycle with
   [Z3aux] (which itself consults [datatype_map] inside [smt_tp_to_sort]). *)
let register_all_for_ctx ctx
    (tp_to_sort : Z3.context -> nt -> Z3.Sort.sort) : unit =
  Hashtbl.clear datatype_map;
  let ordered = topo_sort_decls () in
  List.iter
    (fun decl ->
      let cases =
        List.map
          (fun ctor ->
            let args =
              List.map
                (fun f ->
                  let sort_opt =
                    match f.ftype with
                    | Ty_constructor (n, []) when n = decl.dt_name -> None
                    | nt -> Some (tp_to_sort ctx nt)
                  in
                  (f.fname, sort_opt))
                ctor.fields
            in
            (ctor.cname, args))
          decl.ctors
      in
      let dt = create_data_type ctx decl.dt_name cases in
      Hashtbl.replace datatype_map decl.dt_name dt)
    ordered
