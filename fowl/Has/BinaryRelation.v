(** * Binary Relation *)

From Maniunfold.Has Require Export
  TwoSortedBinaryRelation.

Class HasBinRel (A : Type) : Type := bin_rel : A -> A -> Prop.

Typeclasses Transparent HasBinRel.
