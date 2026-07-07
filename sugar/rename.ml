open SugarAux

(* Source names use a single [split_char]; renamer-issued names carry a doubled
   one ([tag_sep]), so the two never collide and [is_tagged] can tell them apart. *)
let split_char = '_'
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

let is_tagged name = root_of name <> name

(* strip any existing tag before re-tagging, so [unique (unique x)] stays [x__n],
   not [x__n__m] *)
let unique name = spf "%s%s%i" (root_of name) tag_sep (gensym ())
let dummy_var () = unique "dummyVar"
let fresh_type_var () = unique "tv"
let fresh_var () = unique "tmp"
