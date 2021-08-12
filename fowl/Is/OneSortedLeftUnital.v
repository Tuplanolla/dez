From DEZ.Has Require Export
  BinaryOperation NullaryOperation.
From DEZ.Is Require Export
  TwoSortedLeftUnital.
From DEZ.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Unital, having an identity element; left chirality. *)

Class IsUnlL (A : Type)
  `(HasBinOp A) `(HasNullOp A) : Prop :=
  unl_l : forall x : A, 0 + x = x.

Section Context.

Context (A : Type) `{IsUnlL A}.

Global Instance A_A_bin_op_null_op_is_two_unl_l : IsTwoUnlL bin_op null_op.
Proof. intros x. apply unl_l. Defined.

End Context.
