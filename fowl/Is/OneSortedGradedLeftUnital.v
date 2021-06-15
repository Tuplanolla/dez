(* bad *)
From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation
  GradedBinaryOperation GradedNullaryOperation.
From Maniunfold.Is Require Export
  OneSortedLeftUnital.
From Maniunfold.ShouldHave Require Import
  OneSortedGradedAdditiveNotations.

Class IsGrdLUnl (A : Type) (P : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(HasGrdBinOp A P)
  `(HasGrdNullOp A P) : Prop := {
  A_bin_op_null_op_is_l_unl :> IsLUnl bin_op null_op;
  grd_l_unl : forall (i : A) (x : P i), rew l_unl i in (0 + x) = x;
}.
