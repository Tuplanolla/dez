(** * Binary Relation *)

From Maniunfold Require Export
  Init.

Class HasBinRel (A : Type) : Type := bin_rel (x y : A) : Prop.

Typeclasses Transparent HasBinRel.
