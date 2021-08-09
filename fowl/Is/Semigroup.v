(** * Semigroup *)

From DEZ.Has Require Export
  BinaryOperation.
From DEZ.Is Require Export
  Magma Associative.
From DEZ.ShouldHave Require Import
  AdditiveNotations.

Class IsSemigrp (A : Type) (Hk : HasBinOp A) : Prop := {
  is_mag :> IsMag _+_;
  is_assoc :> IsAssoc _+_;
}.
