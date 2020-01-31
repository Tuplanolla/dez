From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation UnaryOperation.
From Maniunfold.Is Require Export
  ExternallyUnaryAntidistributive.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsUnaryAntidistr {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un_op : HasUnOp A) : Prop :=
  un_antidistr : forall x y : A, - (x + y) == - y + - x.

Section Context.

Context {A : Type} `{is_un_antidistr : IsUnaryAntidistr A}.

Global Instance bin_op_un_op_is_ext_un_antidistr :
  IsExtUnaryAntidistr bin_op un_op.
Proof. intros x y. apply un_antidistr. Qed.

End Context.
