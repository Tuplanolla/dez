From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.UnaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Monoid OneSorted.Invertible
  OneSorted.Cancellative OneSorted.UnaryAntidistributive OneSorted.Injective
  OneSorted.Involutive OneSorted.UnaryAbsorbing.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

(** Group, invertible monoid. *)

Class IsGrp (A : Type) (A_has_bin_op : HasBinOp A)
  (A_has_null_op : HasNullOp A) (A_has_un_op : HasUnOp A) : Prop := {
  A_bin_op_null_op_is_mon :> IsMon A bin_op null_op;
  A_bin_op_null_op_un_op_is_inv :> IsInv A bin_op null_op un_op;
}.

Section Context.

Context {A : Type} `{is_grp : IsGrp A}.

Theorem A_bin_op_l_cancel : forall x y z : A,
  z + x = z + y -> x = y.
Proof.
  intros x y z H.
  rewrite <- (l_unl x).
  rewrite <- (l_inv z).
  rewrite <- (assoc (- z) z x).
  rewrite H.
  rewrite (assoc (- z) z y).
  rewrite (l_inv z).
  rewrite (l_unl y).
  reflexivity. Defined.

Global Instance A_bin_op_is_l_cancel : IsLCancel A bin_op.
Proof. intros x y z. apply A_bin_op_l_cancel. Defined.

Theorem A_bin_op_r_cancel : forall x y z : A,
  x + z = y + z -> x = y.
Proof.
  intros x y z H.
  rewrite <- (r_unl x).
  rewrite <- (r_inv z).
  rewrite (assoc x z (- z)).
  rewrite H.
  rewrite <- (assoc y z (- z)).
  rewrite (r_inv z).
  rewrite (r_unl y).
  reflexivity. Defined.

Global Instance A_bin_op_is_r_cancel : IsRCancel A bin_op.
Proof. intros x y z. apply A_bin_op_r_cancel. Defined.

Global Instance A_bin_op_is_cancel : IsCancel A bin_op.
Proof. split; typeclasses eauto. Defined.

Theorem A_bin_op_un_op_un_antidistr : forall x y : A,
  - (x + y) = - y + - x.
Proof.
  intros x y.
  apply (l_cancel (- (x + y)) (- y + - x) (x + y)).
  rewrite (r_inv (x + y)).
  rewrite (assoc (x + y) (- y) (- x)).
  rewrite <- (assoc x y (- y)).
  rewrite (r_inv y).
  rewrite (r_unl x).
  rewrite (r_inv x).
  reflexivity. Defined.

Global Instance A_bin_op_un_op_is_un_antidistr : IsUnAntidistr A bin_op un_op.
Proof. intros x y. apply A_bin_op_un_op_un_antidistr. Defined.

Theorem A_un_op_inj : forall x y : A,
  - x = - y -> x = y.
Proof.
  intros x y H.
  rewrite <- (l_unl y).
  rewrite <- (r_inv x).
  rewrite H.
  rewrite <- (assoc x (- y) y).
  rewrite (l_inv y).
  rewrite (r_unl x).
  reflexivity. Defined.

Global Instance A_un_op_is_inj : IsInj A un_op.
Proof. intros x y. apply A_un_op_inj. Defined.

Theorem A_un_op_invol : forall x : A,
  - - x = x.
Proof.
  intros x.
  rewrite <- (r_unl (- - x)).
  rewrite <- (l_inv x).
  rewrite (assoc (- - x) (- x) x).
  rewrite (l_inv (- x)).
  rewrite (l_unl x).
  reflexivity. Defined.

Global Instance A_un_op_is_invol : IsInvol A un_op.
Proof. intros x. apply A_un_op_invol. Defined.

Theorem A_null_op_un_op_un_absorb : - 0 = 0.
Proof.
  rewrite <- (r_unl (- 0)).
  rewrite (l_inv 0).
  reflexivity. Defined.

Global Instance A_null_op_un_op_is_un_absorb : IsUnAbsorb A null_op un_op.
Proof. apply A_null_op_un_op_un_absorb. Defined.

End Context.
