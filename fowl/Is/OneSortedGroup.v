(** * Group *)

From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation
  UnaryOperation.
From Maniunfold.Is Require Export
  Monoid Invertible
  OneSortedCancellative OneSortedUnaryAntidistributive Injective
  OneSortedInvolutive OneSortedUnaryAbsorbing.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class IsGrp (A : Type)
  (Hx : HasNullOp A) (Hf : HasUnOp A) (Hk : HasBinOp A) : Prop := {
  is_mon :> IsMon 0 _+_;
  is_inv_l_r :> IsInvLR 0 -_ _+_;
}.

Section Context.

Context (A : Type) `(IsGrp A).

(** TODO If we use section notations here,
    the following `Let` becomes useless. *)

Let bin_op : HasBinOp A := bin_op.

Theorem bin_op_l_cancel (x y z : A) (e : z + x = z + y) : x = y.
Proof.
  rewrite <- (unl_bin_op_l x).
  rewrite <- (inv_l z).
  rewrite <- (assoc (- z) z x).
  rewrite e.
  rewrite (assoc (- z) z y).
  rewrite (inv_l z).
  rewrite (unl_bin_op_l y).
  reflexivity. Qed.

Global Instance bin_op_is_l_cancel : IsLCancel bin_op.
Proof. exact @bin_op_l_cancel. Qed.

Theorem bin_op_r_cancel (x y z : A) (e : x + z = y + z) : x = y.
Proof.
  rewrite <- (unl_bin_op_r x).
  rewrite <- (inv_r z).
  rewrite (assoc x z (- z)).
  rewrite e.
  rewrite <- (assoc y z (- z)).
  rewrite (inv_r z).
  rewrite (unl_bin_op_r y).
  reflexivity. Qed.

Global Instance bin_op_is_r_cancel : IsRCancel bin_op.
Proof. exact @bin_op_r_cancel. Qed.

Global Instance bin_op_is_cancel : IsCancel bin_op.
Proof. split; typeclasses eauto. Qed.

Theorem bin_op_un_op_un_antidistr (x y : A) : - (x + y) = (- y) + (- x).
Proof.
  apply (l_cancel (- (x + y)) ((- y) + (- x)) (x + y)).
  rewrite (inv_r (x + y)).
  rewrite (assoc (x + y) (- y) (- x)).
  rewrite <- (assoc x y (- y)).
  rewrite (inv_r y).
  rewrite (unl_bin_op_r x).
  rewrite (inv_r x).
  reflexivity. Qed.

Global Instance bin_op_un_op_is_un_antidistr : IsUnAntidistr bin_op un_op.
Proof. exact @bin_op_un_op_un_antidistr. Qed.

Theorem un_op_inj (x y : A) (e : - x = - y) : x = y.
Proof.
  rewrite <- (unl_bin_op_l y).
  rewrite <- (inv_r x).
  rewrite e.
  rewrite <- (assoc x (- y) y).
  rewrite (inv_l y).
  rewrite (unl_bin_op_r x).
  reflexivity. Qed.

Global Instance un_op_is_inj : IsInj un_op.
Proof. exact @un_op_inj. Qed.

Theorem un_op_invol (x : A) : - (- x) = x.
Proof.
  rewrite <- (unl_bin_op_r (- (- x))).
  rewrite <- (inv_l x).
  rewrite (assoc (- (- x)) (- x) x).
  rewrite (inv_l (- x)).
  rewrite (unl_bin_op_l x).
  reflexivity. Qed.

Global Instance un_op_is_invol : IsInvol un_op.
Proof. exact @un_op_invol. Qed.

Theorem null_op_un_op_un_absorb : - 0 = 0.
Proof.
  rewrite <- (unl_bin_op_r (- 0)).
  rewrite (inv_l 0).
  reflexivity. Qed.

Global Instance null_op_un_op_is_un_absorb : IsUnAbsorb null_op un_op.
Proof. exact @null_op_un_op_un_absorb. Qed.

End Context.
