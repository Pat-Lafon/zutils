open SugarAux

(* A single [_] is ordinary in a source name; a doubled one marks a tag. *)
let tag_sep = "__"
let counter = ref 0

let root_of name =
  let n = String.length name and s = String.length tag_sep in
  let rec digits i =
    if i > 0 && name.[i - 1] >= '0' && name.[i - 1] <= '9' then digits (i - 1)
    else i
  in
  let d = digits n in
  if d < n && d >= s && String.sub name (d - s) s = tag_sep then
    String.sub name 0 (d - s)
  else name

let is_tagged name = root_of name <> name

let unique name =
  let n = !counter in
  incr counter;
  spf "%s%s%i" (root_of name) tag_sep n

let dummy_var () = unique "dummyVar"
let fresh_type_var () = unique "tv"
let fresh_var () = unique "tmp"

(* Misreading a source [<root>_<int>] as tagged is a silent failure. *)
let%test "root_of strips the renamer's tag and nothing else" =
  List.map root_of [ "res_0"; "x__7"; "a__b"; "7"; "x__0__12" ]
  = [ "res_0"; "x"; "a__b"; "7"; "x__0" ]

let%test "unique issues a name it has not issued before" =
  let a = unique "zz" in
  let b = unique "zz" in
  a <> "zz" && b <> "zz" && a <> b

let%test "unique re-tags rather than nesting tags" =
  root_of (unique (unique "x")) = "x"
