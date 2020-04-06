(* bad *)
From Maniunfold Require Export
  Init.

Class HasBinFn (A B C : Type) : Type := bin_fn : A -> B -> C.

Typeclasses Transparent HasBinFn.
