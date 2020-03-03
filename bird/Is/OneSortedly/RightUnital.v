From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit.
From Maniunfold.Is Require Export
  RightUnital.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsRUnl {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop :=
  r_unl : forall x : A, x + 0 == x.

Section Context.

Context {A : Type} `{is_r_unl : IsRUnl A}.

Global Instance un_bin_op_is_two_r_unl_ : IsTwoRUnl un bin_op.
Proof. intros x. apply r_unl. Qed.

End Context.
