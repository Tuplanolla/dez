(** * Arbitrary Function *)

From Maniunfold Require Export
  Init.

#[deprecated (since="now")]
Class HasFn (A B : Type) : Type := fn : A -> B.

#[export] Hint Transparent HasFn : typeclass_instances.
