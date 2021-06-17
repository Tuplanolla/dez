(** * Monoid *)

From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation.
From Maniunfold.Is Require Export
  OneSortedSemigroup OneSortedUnital.

Class IsMon (A : Type) (Hk : HasBinOp A) (Hx : HasNullOp A) : Prop := {
  is_semigrp :> IsSemigrp bin_op;
  is_unl :> IsUnl bin_op null_op;
}.
