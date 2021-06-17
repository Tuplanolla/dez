(** * Involutivity of a Function *)

From Maniunfold Require Export
  Init.

Class IsInvol (A : Type) (f : A -> A) : Prop :=
  invol (x : A) : f (f x) = x.
