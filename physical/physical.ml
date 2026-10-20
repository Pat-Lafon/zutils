(* Opened by every zutils library, with the alert as an error: [==] and [!=]
   compare identity, which agrees with [=] and [<>] only on immediate values. *)

external ( == ) : 'a -> 'a -> bool = "%eq"
[@@alert
  physical
    "compares identity: use = to compare values, or Stdlib.( == ) when \
     identity is meant"]

external ( != ) : 'a -> 'a -> bool = "%noteq"
[@@alert
  physical
    "compares identity: use <> to compare values, or Stdlib.( != ) when \
     identity is meant"]
