open Language
open Normal_regex_typing

type t = Nt.t

let constructor_declaration_mk_ (retty, { constr_name; argsty }) =
  constr_name#:(Nt.construct_arr_tp (argsty, retty))

(* NOTE: the whole spec items are first-order *)
let item_check (ctx : spec_tyctx) (e : t item) : t item =
  match e with
  | MFieldAssign { field; assignment } -> MFieldAssign { field; assignment }
  | MAbstractType x -> MAbstractType x
  | MEventDecl { ev; event_kind } -> MEventDecl { ev; event_kind }
  | MValDecl x -> MValDecl x
  | MRegex { name; automata } ->
      let automata = bi_symbolic_regex_check ctx automata in
      let name = name.x#:automata.ty in
      MRegex { name; automata = automata.x }
  | MClient
      { client_name; event_scope; axioms; type_configs; violation; step_bound }
    ->
      MClient
        {
          client_name;
          event_scope;
          axioms;
          type_configs;
          violation;
          step_bound;
        }

let struct_check ctx l = List.map (item_check ctx) l
