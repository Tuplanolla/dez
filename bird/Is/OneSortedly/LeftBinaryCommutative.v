From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation UnaryOperation.
From Maniunfold.Is Require Import
  LeftExternallyBinaryCommutative.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLBinComm {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un_op : HasUnOp A) : Prop :=
  l_bin_comm : forall x y : A, - (x + y) == - x + y.

Section Context.

Context {A : Type} `{is_l_bin_comm : IsLBinComm A}.

Global Instance bin_op_un_op_is_l_bin_comm : IsLExtBinComm bin_op un_op.
Proof. intros x y. apply l_bin_comm. Qed.

End Context.
