From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation NullaryOperation.
From Maniunfold.Is Require Export
  TwoSortedly.RightUnital.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsRUnl {A : Type} (has_bin_op : HasBinOp A) (has_null_op : HasNullOp A) : Prop :=
  r_unl : forall x : A, x + 0 = x.

Section Context.

Context {A : Type} `{is_r_unl : IsRUnl A}.

Global Instance null_op_bin_op_is_two_r_unl : IsTwoRUnl null_op bin_op.
Proof. intros x. apply r_unl. Qed.

End Context.
