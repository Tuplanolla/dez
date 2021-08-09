(* bad *)
From DEZ.Has Require Export
  BinaryOperation NullaryOperation
  GradedBinaryOperation GradedNullaryOperation.
From DEZ.Is Require Export
  Unital.
From DEZ.ShouldHave Require Import
  OneSortedGradedAdditiveNotations.

Class IsGrdUnlL (A : Type) (P : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(HasGrdBinOp A P)
  `(HasGrdNullOp A P) : Prop := {
  A_bin_op_null_op_is_unl_l :> IsUnlBinOpL null_op bin_op;
  grd_unl_l : forall (i : A) (x : P i), rew unl_bin_op_l i in (0 + x) = x;
}.
