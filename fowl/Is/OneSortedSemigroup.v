(** * Semigroup or Associative Magma *)

From Maniunfold.Has Require Export
  BinaryOperation.
From Maniunfold.Is Require Export
  OneSortedMagma Associative.

Class IsSemigrp (A : Type) (Hk : HasBinOp A) : Prop := {
  is_mag :> IsMag bin_op;
  is_assoc :> IsAssoc bin_op;
}.
