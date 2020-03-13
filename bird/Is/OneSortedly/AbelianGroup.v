From Maniunfold.Has.OneSorted Require Export
  BinaryOperation Unit UnaryOperation.
From Maniunfold.Is.OneSortedly Require Export
  Commutative Group UnaryDistributive.
From Maniunfold.ShouldHave.OneSorted Require Import
  AdditiveNotations.

Class IsAbGrp {A : Type}
  (has_bin_op : HasBinOp A) (has_un : HasUn A)
  (has_un_op : HasUnOp A) : Prop := {
  bin_op_is_comm :> IsComm bin_op;
  bin_op_un_un_op_is_grp :> IsGrp bin_op un un_op;
}.

Section Context.

Context {A : Type} `{is_ab_grp : IsAbGrp A}.

Theorem bin_op_un_op_un_distr : forall x y : A,
  - (x + y) = - x + - y.
Proof.
  intros x y.
  rewrite (comm x y).
  rewrite (un_antidistr y x).
  reflexivity. Qed.

Global Instance bin_op_un_op_is_un_distr : IsUnDistr bin_op un_op.
Proof. intros x y. apply bin_op_un_op_un_distr. Qed.

End Context.
