From DEZ.Has Require Export
  BinaryOperation NullaryOperation.
From DEZ.Is Require Export
  TwoSortedRightUnital.
From DEZ.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Unital; right chirality.
    See [Is.OneSortedLeftUnital]. *)

Class IsUnlR (A : Type)
  `(HasBinOp A) `(HasNullOp A) : Prop :=
  unl_r : forall x : A, x + 0 = x.

Section Context.

Context (A : Type) `{IsUnlR A}.

Global Instance A_A_bin_op_null_op_is_two_unl_r : IsTwoUnlR bin_op null_op.
Proof. intros x. apply unl_r. Defined.

End Context.
