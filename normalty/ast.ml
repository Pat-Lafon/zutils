open Sugar
open Sexplib.Std

(** Quantifiers *)

type qt = Fa | Ex [@@deriving sexp, show, eq, ord]
type binary = Implies | Iff [@@deriving sexp, show, eq, ord]
type multi = And | Or [@@deriving sexp, show, eq, ord]

let is_forall = function Fa -> true | Ex -> false
let is_exists x = not @@ is_forall x

let qt_of_string = function
  | "forall" -> Fa
  | "exists" -> Ex
  | _ -> failwith "not a quantifier"

let qt_to_string = function Fa -> "forall" | Ex -> "exists"
let qt_pretty_layout = function Fa -> "∀ " | Ex -> "∃ "

(** Type used for smt query. *)

type smtty =
  | Smt_Unit
  | Smt_Bool
  | Smt_Int
  | Smt_Char
  | Smt_String
  | Smt_Float64
  | Smt_option of smtty
  | Smt_tuple of smtty list
  | Smt_record of (smtty, string) typed list
  | Smt_Uninterp of string
[@@deriving sexp, show, eq, ord, yojson]

(** Normal Type. *)

type nt =
  | Ty_unknown (* parsing only, equal to none *)
  | Ty_var of string
  | Ty_arrow of nt * nt
  | Ty_tuple of nt list
  | Ty_constructor of (string * nt list)
  | Ty_record of { alias : string option; fds : (nt, string) typed list }
    (* NOTE: alias for print only *)
  | Ty_poly of string * nt
    (* We only allow poly type appear at 1. top level 2. return type of arrow *)
[@@deriving sexp, eq, show, ord, yojson]

type t = nt

open Sugar

let is_uninterp = function Smt_Uninterp _ -> true | _ -> false

let rec is_base_tp = function
  | Ty_poly (_, _) | Ty_arrow _ -> false
  | Ty_constructor _ | Ty_var _ -> true
  | Ty_record { fds; _ } -> List.for_all (fun x -> is_base_tp x.ty) fds
  | Ty_tuple l -> List.for_all is_base_tp l
  | _ -> false

(* let is_basic_tp = function Ty_enum _ -> true | _ -> false *)
let _constructor_ty_0 name = Ty_constructor (name, [])
let unit_ty = _constructor_ty_0 "unit"
let bool_ty = _constructor_ty_0 "bool"
let int_ty = _constructor_ty_0 "int"
let nat_ty = _constructor_ty_0 "nat"
let char_ty = _constructor_ty_0 "char"
let string_ty = _constructor_ty_0 "string"
let float_ty = _constructor_ty_0 "float"
let is_dt = function Ty_constructor _ -> true | _ -> false
let fst_ty = function Ty_tuple [ a; _ ] -> a | _ -> _die [%here]
let snd_ty = function Ty_tuple [ _; a ] -> a | _ -> _die [%here]
let para_ty = function Ty_arrow (t, _) -> t | _ -> _die [%here]
let ret_ty = function Ty_arrow (_, t) -> t | _ -> _die [%here]
let mk_record alias fds = Ty_record { alias; fds }

let get_record_types = function
  | Ty_record { fds; _ } -> fds
  | _ -> _die [%here]

let get_nth_ty loc ty n =
  match ty with
  | Ty_tuple l -> (
      match List.nth_opt l n with
      | None ->
          _die_with loc
          @@ spf "cannot find %i th element of tuple type %s" n (show_nt ty)
      | Some ty -> ty)
  | _ -> _die_with loc "not a tuple type"

let get_arr_lhs = function Ty_arrow (t1, _) -> t1 | _ -> _die [%here]
let get_arr_rhs = function Ty_arrow (_, t2) -> t2 | _ -> _die [%here]
