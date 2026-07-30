open Language
open Normal_regex_typing

type t = Nt.t

let unfold_sort sort_ctx ty =
  match get_opt sort_ctx (Nt.layout ty) with None -> ty | Some ty' -> ty'

let bi_qregex_check (regex_check : t ctx -> 'a regex -> 'b regex) (ctx : t ctx)
    (qregex : (Nt.t option, 'a) qregex) : (Nt.t, 'b) qregex =
  let rec aux sort_ctx ctx qregex =
    match qregex with
    | RPi { sort; body } ->
        let sort = __force_typed [%here] sort in
        let sort_ctx = add_to_right sort_ctx sort in
        RPi { sort; body = aux sort_ctx ctx body }
    | Regex regex -> Regex (regex_check ctx regex)
    | RForall { qv; body } ->
        let qv = __force_typed [%here] qv in
        let qv' = qv.x#:(unfold_sort sort_ctx qv.ty) in
        RForall { qv; body = aux sort_ctx (add_to_right ctx qv') body }
    | RExists { qv; body } ->
        let qv = __force_typed [%here] qv in
        let qv' = qv.x#:(unfold_sort sort_ctx qv.ty) in
        RExists { qv; body = aux sort_ctx (add_to_right ctx qv') body }
  in
  aux emp ctx qregex

let bi_str_qregex_check ctx automata =
  bi_qregex_check bi_str_regex_check ctx automata

let bi_symbolic_qregex_check ctx automata =
  bi_qregex_check bi_symbolic_regex_check ctx automata
