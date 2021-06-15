From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation.
From Maniunfold.Is Require Export
  TwoSortedRightUnital.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Unital; right chirality.
    See [Is.OneSortedLeftUnital]. *)

Class IsRUnl (A : Type)
  `(HasBinOp A) `(HasNullOp A) : Prop :=
  r_unl : forall x : A, x + 0 = x.

Section Context.

Context (A : Type) `{IsRUnl A}.

Global Instance A_A_bin_op_null_op_is_two_r_unl : IsTwoRUnl bin_op null_op.
Proof. intros x. apply r_unl. Defined.

End Context.
