(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation.
From Maniunfold.Is Require Export
  TwoSorted.RightUnital.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class IsRUnl {A : Type}
  (A_has_bin_op : HasBinOp A) (A_has_null_op : HasNullOp A) : Prop :=
  r_unl : forall x : A, x + 0 = x.

Section Context.

Context {A : Type} `{is_r_unl : IsRUnl A}.

Global Instance A_A_null_op_bin_op_is_two_r_unl : IsTwoRUnl A A null_op bin_op.
Proof. intros x. apply r_unl. Qed.

End Context.
