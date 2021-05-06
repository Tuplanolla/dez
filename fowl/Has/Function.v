(** * Operational class for arbitrary functions. *)

From Maniunfold Require Export
  Init.

Class HasFn (A B : Type) : Type := fn : A -> B.

#[export] Hint Transparent HasFn : typeclass_instances.
