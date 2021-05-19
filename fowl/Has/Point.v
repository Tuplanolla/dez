(** * Operational class for arbitrary points. *)

From Maniunfold Require Export
  Init.

Class HasPt (A : Type) : Type := pt : A.

#[export] Hint Transparent HasPt : typeclass_instances.
