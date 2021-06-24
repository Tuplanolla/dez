From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation.
From Maniunfold.Is Require Export
  TwoSortedRightUnital.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Unital; right chirality.
    See [Is.OneSortedLeftUnital]. *)

Class IsUnlBinOpR (A : Type)
  `(HasBinOp A) `(HasNullOp A) : Prop :=
  unl_bin_op_r : forall x : A, x + 0 = x.

Section Context.

Context (A : Type) `{IsUnlBinOpR A}.

Global Instance A_A_bin_op_null_op_is_two_unl_r : IsTwoUnlR bin_op null_op.
Proof. intros x. apply unl_bin_op_r. Defined.

End Context.
