From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit.
From Maniunfold.Is Require Export
  TwoSortedly.LeftUnital.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLUnl {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop :=
  l_unl : forall x : A, 0 + x == x.

Section Context.

Context {A : Type} `{is_l_unl : IsLUnl A}.

Global Instance un_bin_op_is_l_unl_2 : IsLUnl2 un bin_op.
Proof. intros x. apply l_unl. Qed.

End Context.
