open Z3
open Z3aux
open Syntax
open Sugar

let get_idx_in_list x l =
  let rec aux i = function
    | [] -> _die [%here]
    | h :: l -> if String.equal x h then i else aux (i + 1) l
  in
  aux 0 l

let constant_to_z3 env c =
  let aux c =
    match c with
    | U -> Enumeration.get_const (tp_to_sort env Nt.unit_ty) 0
    | B b -> bool_to_z3 env b
    | I i -> int_to_z3 env i
    | C c -> char_to_z3 env c
    | S s -> str_to_z3 env s
    | F f -> float_to_z3 env f
  in
  aux c
