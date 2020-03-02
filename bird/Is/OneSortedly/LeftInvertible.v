From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit UnaryOperation.
From Maniunfold.Is Require Export
  LeftExternallyInvertible.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLInv {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A)
  (has_un_op : HasUnOp A) : Prop :=
  l_inv : forall x : A, - x + x == 0.

Section Context.

Context {A : Type} `{is_l_inv : IsLInv A}.

Global Instance bin_op_un_un_op_is_l_ext_inv : IsLExtInv un un_op bin_op.
Proof. intros x. apply l_inv. Qed.

End Context.
