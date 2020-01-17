From Maniunfold Require Export
  Init.

Class HasBiRel (A : Type) : Type := bi_rel : A -> A -> Prop.

Typeclasses Transparent HasBiRel.
