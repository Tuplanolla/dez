From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation.
From Maniunfold.Is Require Export
  TwoSortedly.LeftUnital.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class IsLUnl {A : Type}
  (A_has_bin_op : HasBinOp A) (A_has_null_op : HasNullOp A) : Prop :=
  l_unl : forall x : A, 0 + x = x.

Section Context.

Context {A : Type} `{is_l_unl : IsLUnl A}.

Global Instance null_op_bin_op_is_two_l_unl : IsTwoLUnl null_op bin_op.
Proof. intros x. apply l_unl. Qed.

End Context.
