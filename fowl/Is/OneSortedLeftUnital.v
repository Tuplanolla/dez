From Maniunfold.Has Require Export
  BinaryOperation OneSortedNullaryOperation.
From Maniunfold.Is Require Export
  TwoSortedLeftUnital.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Unital, having an identity element; left chirality. *)

Class IsLUnl (A : Type)
  `(HasBinOp A) `(HasNullOp A) : Prop :=
  l_unl : forall x : A, 0 + x = x.

Section Context.

Context (A : Type) `{IsLUnl A}.

Global Instance A_A_bin_op_null_op_is_two_l_unl : IsTwoLUnl bin_op null_op.
Proof. intros x. apply l_unl. Defined.

End Context.
