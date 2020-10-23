From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation.
From Maniunfold.Is Require Export
  TwoSorted.LeftUnital.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

(** Unital, having an identity element; left chirality. *)

Class IsLUnl (A : Type)
  `(HasBinOp A) `(HasNullOp A) : Prop :=
  l_unl : forall x : A, 0 + x = x.

Section Context.

Context {A : Type} `{IsLUnl A}.

Global Instance A_A_bin_op_null_op_is_two_l_unl : IsTwoLUnl A A bin_op null_op.
Proof. intros x. apply l_unl. Defined.

End Context.
