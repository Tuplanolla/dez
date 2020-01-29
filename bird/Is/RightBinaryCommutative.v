From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation UnaryOperation.
From Maniunfold.Is Require Import
  RightExternallyBinaryCommutative.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsRBinComm {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un_op : HasUnOp A) : Prop :=
  r_bin_comm : forall x y : A, - (x + y) == x + - y.

Section Context.

Context {A : Type} `{is_r_bin_comm : IsRBinComm A}.

Global Instance bin_op_un_op_is_r_bin_comm : IsRExtBinComm bin_op un_op.
Proof. intros x y. apply r_bin_comm. Qed.

End Context.
