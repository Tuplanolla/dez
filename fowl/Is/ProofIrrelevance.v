(** * Proof Irrelevance *)

From Maniunfold Require Export
  Init.

Class IsIrrel (A : Type) : Prop :=
  irrel (x y : A) : x = y.
