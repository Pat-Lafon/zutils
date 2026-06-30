open SugarAux

let split_char = '_'

(* [tag_sep] is a doubled separator, keeping generated names disjoint from
   source names (which use single separators). [unique] re-tags by stripping any
   prior tag first ([root_of]), so repeated renames stay bounded. *)
let tag_sep = spf "%c%c" split_char split_char
let counter = ref 0

let gensym () =
  let n = !counter in
  incr counter;
  n

let root_of name =
  let n = String.length name and s = String.length tag_sep in
  let rec last_tag i =
    if i < 0 then None
    else if name.[i] = split_char && name.[i + 1] = split_char then Some i
    else last_tag (i - 1)
  in
  match last_tag (n - s) with
  | Some i ->
      let tail = String.sub name (i + s) (n - i - s) in
      if
        tail <> ""
        && String.for_all (function '0' .. '9' -> true | _ -> false) tail
      then String.sub name 0 i
      else name
  | None -> name

(* A name is renamer-issued iff it carries a [tag_sep] tag that [root_of] strips. *)
let is_tagged name = root_of name <> name
let unique name = spf "%s%s%i" (root_of name) tag_sep (gensym ())
let dummy_var () = unique "dummyVar"
let fresh_type_var () = unique "tv"
let fresh_var () = unique "tmp"
