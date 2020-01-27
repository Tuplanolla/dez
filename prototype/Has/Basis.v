From Maniunfold Require Export
  Init.

Class HasBasis (I A : Type) : Type := basis : I -> A.

Typeclasses Transparent HasBasis.
