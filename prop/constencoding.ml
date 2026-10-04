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

let constant_to_z3 ctx c =
  let aux c =
    match c with
    | U -> Enumeration.get_const (tp_to_sort ctx Nt.unit_ty) 0
    | B b -> bool_to_z3 ctx b
    | I i -> int_to_z3 ctx i
    | C c -> char_to_z3 ctx c
    | S s -> str_to_z3 ctx s
    | F f -> float_to_z3 ctx f
  in
  aux c
