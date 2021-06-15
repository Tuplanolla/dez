(* bad *)
From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation
  GradedBinaryOperation GradedNullaryOperation.
From Maniunfold.Is Require Export
  OneSortedRightUnital.
From Maniunfold.ShouldHave Require Import
  OneSortedGradedAdditiveNotations.

Class IsGrdRUnl (A : Type) (P : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(HasGrdBinOp A P)
  `(HasGrdNullOp A P) : Prop := {
  bin_op_null_op_is_r_unl :> IsRUnl bin_op null_op;
  grd_r_unl : forall (i : A) (x : P i), rew r_unl i in (x + 0) = x;
}.
