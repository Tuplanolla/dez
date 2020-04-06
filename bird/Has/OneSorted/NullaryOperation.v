From Maniunfold Require Export
  Init.

(** Nullary operation, unit, identity, neutral element.
    Commonly found in monoids. *)

Class HasNullOp (A : Type) : Type := null_op : A.

Typeclasses Transparent HasNullOp.
