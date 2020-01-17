From Maniunfold Require Export
  Init.

Class HasBinFn (A B C : Type) : Type := bi_fn : A -> B -> C.

Typeclasses Transparent HasBinFn.
