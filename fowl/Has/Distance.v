(** * Distance or Metric *)

From Maniunfold Require Export
  Init.

Class HasDist (A B : Type) : Type := dist (x y : A) : B.

Typeclasses Transparent HasDist.
