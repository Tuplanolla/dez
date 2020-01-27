From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation UnaryOperation.
From Maniunfold.Is Require Export
  ExternallyAntidistributive.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsAntidistr {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un_op : HasUnOp A) : Prop :=
  antidistr : forall x y : A, - (x + y) == - y + - x.

Section Context.

Context {A : Type} `{is_antidistr : IsAntidistr A}.

Global Instance bin_op_un_op_is_ext_antidistr : IsExtAntidistr bin_op un_op.
Proof. intros x y. apply antidistr. Qed.

End Context.
