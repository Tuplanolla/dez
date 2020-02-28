From Maniunfold Require Export
  Init.

Class HasBinRel2 (A B : Type) : Type := bin_rel_2 : A -> B -> Prop.

Typeclasses Transparent HasBinRel2.
