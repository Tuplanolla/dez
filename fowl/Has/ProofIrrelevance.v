(** * Proof Irrelevance *)

From Maniunfold Require Export
  Init.

Class HasIrrel (A : Type) : Type := irrel (x y : A) : x = y.

Typeclasses Transparent HasIrrel.
