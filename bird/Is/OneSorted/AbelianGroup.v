From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.UnaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Commutative OneSorted.Group OneSorted.UnaryDistributive.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

(** Abelian group, commutative group. *)

Class IsAbGrp (A : Type) (A_has_bin_op : HasBinOp A)
  (A_has_null_op : HasNullOp A) (A_has_un_op : HasUnOp A) : Prop := {
  A_bin_op_is_comm :> IsComm A bin_op;
  A_bin_op_null_op_un_op_is_grp :> IsGrp A bin_op null_op un_op;
}.

Section Context.

Context {A : Type} `{is_ab_grp : IsAbGrp A}.

Theorem A_bin_op_un_op_un_distr : forall x y : A,
  - (x + y) = - x + - y.
Proof.
  intros x y.
  rewrite (comm x y).
  rewrite (un_antidistr y x).
  reflexivity. Qed.

Global Instance A_bin_op_un_op_is_un_distr : IsUnDistr A bin_op un_op.
Proof. intros x y. apply A_bin_op_un_op_un_distr. Qed.

End Context.
