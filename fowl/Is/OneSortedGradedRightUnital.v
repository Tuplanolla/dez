(* bad *)
From DEZ.Has Require Export
  BinaryOperation NullaryOperation
  GradedBinaryOperation GradedNullaryOperation.
From DEZ.Is Require Export
  Unital.
From DEZ.ShouldHave Require Import
  OneSortedGradedAdditiveNotations.

Class IsGrdUnlR (A : Type) (P : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(HasGrdBinOp A P)
  `(HasGrdNullOp A P) : Prop := {
  bin_op_null_op_is_unl_r :> IsUnlR null_op bin_op;
  grd_unl_r : forall (i : A) (x : P i), rew unl_r i in (x + 0) = x;
}.
