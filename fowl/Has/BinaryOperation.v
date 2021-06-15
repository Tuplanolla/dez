(** * Binary Operation *)

From Maniunfold Require Export
  Init.

Class HasBinOp (A : Type) : Type := bin_op (x y : A) : A.

Typeclasses Transparent HasBinOp.
