From Maniunfold Require Export
  Init.

Class HasBinRel (A : Type) : Type := bin_rel : A -> A -> Prop.

Typeclasses Transparent HasBinRel.
