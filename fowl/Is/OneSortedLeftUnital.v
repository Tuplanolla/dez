From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation.
From Maniunfold.Is Require Export
  TwoSortedLeftUnital.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Unital, having an identity element; left chirality. *)

Class IsUnlBinOpL (A : Type)
  `(HasBinOp A) `(HasNullOp A) : Prop :=
  unl_bin_op_l : forall x : A, 0 + x = x.

Section Context.

Context (A : Type) `{IsUnlBinOpL A}.

Global Instance A_A_bin_op_null_op_is_two_unl_l : IsTwoUnlL bin_op null_op.
Proof. intros x. apply unl_bin_op_l. Defined.

End Context.
