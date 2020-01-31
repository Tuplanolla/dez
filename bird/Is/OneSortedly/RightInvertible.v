From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit UnaryOperation.
From Maniunfold.Is Require Export
  RightExternallyInvertible.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsRInv {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A)
  (has_un_op : HasUnOp A) : Prop :=
  r_inv : forall x : A, x + - x == 0.

Section Context.

Context {A : Type} `{is_r_inv : IsRInv A}.

Global Instance bin_op_un_un_op_is_r_ext_inv : IsRExtInv bin_op un un_op.
Proof. intros x. apply r_inv. Qed.

End Context.
