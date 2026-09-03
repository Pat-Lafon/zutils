open Sexplib.Std
open Sugar
module Nt = Normalty

type op = PrimOp of string | DtConstructor of string
[@@deriving sexp, show, eq, ord, yojson]

(* a string:
   1. is in builtin_primop, then is a builtin operator.
   2. is in not builtin_primop, and with a non-lowercase alphabeta first char, then is a data constructor (include [])
   3. else, invalid
*)

let builtin_primop =
  [
    "+";
    "-";
    "*";
    "/";
    "^";
    ">";
    ">=";
    "<";
    "<=";
    "==";
    "!=";
    "&&";
    "||";
    "not";
    "mod";
    "char_is_digit";
    "char_to_int";
    "char_le";
  ]

let eq_op = "=="
let is_builtin_op str = List.exists (String.equal str) builtin_primop

(* The constant can be direct encoded into z3 literal *)
(* The constant is self-typed *)
(* The constant has literal that can be passed directly *)
(* NOTE: None and other enum literals are lit because they are not self-typed *)
type constant =
  | U
  | B of bool
  | I of int
  | C of char
  | S of string
  | F of float
[@@deriving sexp, show, eq, ord, yojson]

type 't lit =
  | AC of constant
  | AVar of (('t, string) typed[@free])
  | ATu of ('t, 't lit) typed list
  | AProj of ('t, 't lit) typed * int
  | ARecord of (string * ('t, 't lit) typed) list
  | AField of ('t, 't lit) typed * string
  | AAppOp of ('t, string) typed * ('t, 't lit) typed list
    (* NOTE: includes None, emum, data constructor, primitive operators *)
[@@deriving sexp, show, eq, ord, yojson]

let proj_func = "_proj"
let fst_func = "fst"
let snd_func = "snd"

type 't prop =
  | Lit of ('t, 't lit) typed
  | Implies of 't prop * 't prop
  | Ite of 't prop * 't prop * 't prop
  | Not of 't prop
  | And of 't prop list
  | Or of 't prop list
  | Iff of 't prop * 't prop
  | Forall of { qv : (('t, string) typed[@bound]); body : 't prop }
  | Exists of { qv : (('t, string) typed[@bound]); body : 't prop }
[@@deriving sexp, show, eq, ord]

let eq_lit p1 p2 = equal_lit (fun _ _ -> true) p1 p2
let eq_prop p1 p2 = equal_prop (fun _ _ -> true) p1 p2

(** Ast builder *)

let uAVar x = AVar (Nt.untyped x)

let sort_lit_record args =
  if ZUtilsConfig.get_if_sort_record () then
    List.sort (fun a b -> String.compare (fst a) (fst b)) args
  else args

let mk_lit_record args = ARecord (sort_lit_record args)

let as_lit_record loc = function
  | ARecord args -> sort_lit_record args
  | _ -> _die loc

let get_lit_field loc t name =
  let args = as_lit_record loc t in
  match List.find_opt (fun y -> String.equal name (fst y)) args with
  | None -> _die [%here]
  | Some n -> snd n

let get_lit_field_idx loc t name =
  let args = as_lit_record loc t in
  match List.find_index (fun y -> String.equal name (fst y)) args with
  | None -> _die [%here]
  | Some n -> n

open Zdatatype

let unified_axiom_type_var = "a"

type laxiom = { preds : StrSet.t; prop : Nt.t prop; z3_prop : Z3.Expr.expr }
type laxiom_system = laxiom StrMap.t
