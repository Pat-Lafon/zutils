(* Store func_decls rather than re-derive them: re-deriving an already-defined
   recursive function via Z3's [mk_rec_func_decl_s] segfaults Z3 in the real
   serialization flow. *)
type rec_func_map = (string, Z3.FuncDecl.func_decl) Hashtbl.t

let register_rec_func (map : rec_func_map) (name : string)
    (fd : Z3.FuncDecl.func_decl) : unit =
  if Hashtbl.mem map name then
    failwith
      (Printf.sprintf "Func_encoding: duplicate functional symbol %s" name);
  Hashtbl.add map name fd

let lookup (map : rec_func_map) (name : string) : Z3.FuncDecl.func_decl option =
  Hashtbl.find_opt map name
