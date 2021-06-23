(** * Monoid *)

From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation.
From Maniunfold.Is Require Export
  OneSortedSemigroup OneSortedUnital.

Class IsMon (A : Type) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop := {
  is_semigrp :> IsSemigrp bin_op;
  is_unl :> IsUnl bin_op null_op;
}.
