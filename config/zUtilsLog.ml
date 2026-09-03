let tagged tag (f : unit -> unit) =
  if List.exists (String.equal tag) (ZUtilsConfig.get_log_tags ()) then f ()

let axiom = tagged "axiom"
let simpl_prop = tagged "simplProp"
let unification = tagged "unification"
let z3encode = tagged "z3encode"
let queries = tagged "queries"
let dump_smt = tagged "dump_smt"
let stat = tagged "stat"
let debug = tagged "debug"
