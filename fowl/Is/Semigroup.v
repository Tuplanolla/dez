(** * Semigroup *)

From Maniunfold.Has Require Export
  BinaryOperation.
From Maniunfold.Is Require Export
  Magma Associative.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class IsSemigrp (A : Type) (Hk : HasBinOp A) : Prop := {
  is_mag :> IsMag _+_;
  is_assoc :> IsAssoc _+_;
}.
