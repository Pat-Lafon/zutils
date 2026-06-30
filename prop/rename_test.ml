open Syntax
open Sugar

(* The tests below print props, and the printer reads the global zutils config,
   which crashes if nobody set it. There's no entry point here to load a real one,
   so seed it with the defaults. *)
let () = ZUtilsConfig.set ZUtilsConfig.default

(* Regression tests for [fresh_name_prop] and [instantiate_quantified_bool].
   [well_renamed] is the contract every input below is checked against. *)

let eqp a b = Lit (mk_var_eq_var [%here] a#:Nt.int_ty b#:Nt.int_ty)#:Nt.bool_ty
let fa name body = Forall { qv = name#:Nt.int_ty; body }
let ex name body = Exists { qv = name#:Nt.int_ty; body }
let free_names p = List.sort_uniq String.compare (List.map _get_x (fv_prop p))

(* Rename each binder to its nesting depth, using the ["$"] namespace that no
   source name uses so renaming can't accidentally capture. Two props get the
   same canonical form exactly when they're alpha-equivalent: depth depends only
   on nesting, not names, so a capture lands an occurrence on a different binder
   and changes its depth. And/Or go through [fresh_name_prop]'s smart
   constructors so both sides normalize the same way — a raw And/Or here would
   look different from the renamer's output for no real reason. *)
let canonicalize_binders prop =
  let rec go depth p =
    let quant qv body =
      let nm = "$" ^ string_of_int depth in
      ( nm#:qv.ty,
        go (depth + 1) (subst_prop_instance qv.x (AVar nm#:qv.ty) body) )
    in
    match p with
    | Forall { qv; body } ->
        let qv, body = quant qv body in
        Forall { qv; body }
    | Exists { qv; body } ->
        let qv, body = quant qv body in
        Exists { qv; body }
    | And l -> smart_and (List.map (go depth) l)
    | Or l -> smart_or (List.map (go depth) l)
    | Implies (a, b) -> Implies (go depth a, go depth b)
    | Iff (a, b) -> Iff (go depth a, go depth b)
    | Ite (a, b, c) -> Ite (go depth a, go depth b, go depth c)
    | Not a -> Not (go depth a)
    | Lit _ -> p
  in
  go 0 prop

(* Use [equal_prop Nt.equal_nt] rather than [eq_prop] so that a renamer which
   corrupts a bound variable's type is also caught, not just one that misnames. *)
let alpha_eq a b =
  equal_prop Nt.equal_nt (canonicalize_binders a) (canonicalize_binders b)

(* Three things a good renaming must hold: quantifier names stay unique (needed
   by [Propencoding.to_z3], which keys quantifiers by name), nothing gets
   captured (alpha_eq), and no free variable changes (free_names). *)
let well_renamed original =
  let renamed = fresh_name_prop original in
  Propencoding.unique_quantifiers renamed
  && alpha_eq original renamed
  && free_names original = free_names renamed

(* A hard case for capture: the inner [idx20_7] shadows the outer one, while the
   [idx20_8] conjunct still refers to the outer [idx20_7], and the [_N] suffixes
   are real source names the renamer mustn't mangle. If it merges the two binders
   or sends a reference to the wrong one, alpha_eq or unique_quantifiers fails. *)
let%test "fresh_name_prop: shadowing and references" =
  well_renamed
    (fa "idx20_7"
       (And
          [
            eqp "idx20_7" "w";
            ex "idx20_7" (eqp "idx20_7" "z");
            fa "idx20_8" (eqp "idx20_7" "idx20_8");
          ]))

(* Expanding a bool quantifier copies its body into both conjuncts, so the body's
   binder must be freshened or the result carries two same-named quantifiers. *)
let%test "instantiate_quantified_bool keeps quantifiers unique" =
  Propencoding.unique_quantifiers
    (SimplProp.instantiate_quantified_bool
       (Forall
          {
            qv = "bq"#:Nt.bool_ty;
            body =
              fa "xq_1"
                (Iff (Lit (tvar_to_lit "bq"#:Nt.bool_ty), eqp "xq_1" "w"));
          }))
