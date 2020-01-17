From Maniunfold Require Export
  Init.

Class HasBiFn (A B C : Type) : Type := bi_fn : A -> B -> C.

Typeclasses Transparent HasBiFn.
