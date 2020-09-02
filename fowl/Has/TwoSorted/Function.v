From Maniunfold Require Export
  Init.

(** Function, mapping. *)

Class HasFn (A B : Type) : Type := fn : A -> B.

Typeclasses Transparent HasFn.
