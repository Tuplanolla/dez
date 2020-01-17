From Maniunfold Require Export
  Init.

Class HasBinRel (A : Type) : Type := bi_rel : A -> A -> Prop.

Typeclasses Transparent HasBinRel.
