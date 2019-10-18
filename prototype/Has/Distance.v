From Maniunfold Require Export
  Init.

Class HasDist (S A : Type) : Type := dist : A -> A -> S.

Typeclasses Transparent HasDist.
