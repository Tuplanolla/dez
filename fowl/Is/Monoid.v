(** * Monoid *)

From DEZ.Has Require Export
  NullaryOperation BinaryOperation.
From DEZ.Is Require Export
  Semigroup Unital.
From DEZ.ShouldHave Require Import
  AdditiveNotations.

Class IsMon (A : Type) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop := {
  is_semigrp :> IsSemigrp _+_;
  is_unl_bin_op_l_r :> IsUnlBinOpLR 0 _+_;
}.
