open OcamlParser
open Sugar
open Parsetree
open Ast_helper
module Nt = Normalty

let mk_app_expr func args =
  let args = List.map (fun x -> (Asttypes.Nolabel, x)) args in
  Exp.apply func args

let typed_to_expr f expr =
  match expr.ty with
  | None -> f expr.x
  | Some ty -> Exp.constraint_ (f expr.x) (Nt.t_to_core_type ty)

let update_ty { x; ty } ty' =
  match ty with None -> x#:(Some ty') | Some _ -> x#:(Some ty')

let notated (name, t) =
  Typ.extension (Location.mknoloc name, PTyp (Nt.t_to_core_type t))

let quantifier_to_pattern (q, u) =
  let x = Pat.var (Location.mknoloc u.x) in
  let x =
    match q with
    | Nt.Fa -> x
    | _ ->
        Pat.attr x @@ Attr.mk (Location.mknoloc (Nt.qt_to_string q)) (PStr [])
  in
  Pat.constraint_ x (Nt.t_to_core_type u.ty)

let smt_layout_ty = function
  | Some (Nt.Ty_constructor ("bool", [])) -> "Bool"
  | Some (Nt.Ty_constructor ("int", [])) -> "Int"
  | Some (Nt.Ty_constructor ("char", [])) -> "Char"
  | Some (Nt.Ty_constructor ("string", [])) -> "String"
  | Some (Nt.Ty_constructor ("float", [])) -> "Float64"
  | Some (Nt.Ty_constructor _) -> "Int"
  | _ -> _die_with [%here] "unimp"

type 't layout_setting = {
  sym_true : string;
  sym_false : string;
  sym_and : string;
  sym_or : string;
  sym_not : string;
  sym_implies : string;
  sym_iff : string;
  sym_forall : string;
  sym_exists : string;
  layout_typedid : ('t, string) typed -> string;
  layout_mp : string -> string;
}

let detailssetting =
  {
    sym_true = "⊤";
    sym_false = "⊥";
    sym_and = " 𐌡 ";
    sym_or = " ᐯ ";
    sym_not = "¬";
    sym_implies = "=>";
    sym_iff = "<=>";
    sym_forall = "∀";
    sym_exists = "∃";
    layout_typedid = Nt.(fun x -> spf "(%s:%s)" x.x (layout x.ty));
    layout_mp = (fun x -> x);
  }

let psetting =
  {
    sym_true = "⊤";
    sym_false = "⊥";
    sym_and = " 𐌡 ";
    sym_or = " ᐯ ";
    sym_not = "¬";
    sym_implies = "=>";
    sym_iff = "<=>";
    sym_forall = "∀";
    sym_exists = "∃";
    layout_typedid = (fun x -> x.x);
    (* (fun x ->          Printf.spf "(%s:%s)" x.x (Ty.layout x.ty)); *)
    layout_mp = (fun x -> x);
  }

let rec coq_layout_ty = function
  | Nt.Ty_constructor (name, _) -> (
      match name with
      | "bool" -> "bool"
      | "int" -> "Z"
      | "unit" -> "unit"
      | _ -> name)
  | Nt.Ty_tuple tys -> String.concat " * " (List.map coq_layout_ty tys)
  | ty ->
      _die_with [%here]
        (spf "coq_layout_ty: unsupported type '%s'" (Nt.layout ty))

(* Coq needs the binder's type — [forall (x : Z), ...] — and spells disequality
   [<>]. *)
let coqsetting =
  {
    sym_true = "True";
    sym_false = "False";
    sym_and = " /\\ ";
    sym_or = " \\/ ";
    sym_not = "~";
    sym_implies = "->";
    sym_iff = "<->";
    sym_forall = "forall ";
    sym_exists = "exists ";
    layout_typedid = (fun x -> spf "(%s : %s)" x.x (coq_layout_ty x.ty));
    layout_mp = (function "==" -> "=" | "!=" -> "<>" | x -> x);
  }
