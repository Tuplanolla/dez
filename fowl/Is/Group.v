(** * Group *)

From Maniunfold.Has Require Export
  NullaryOperation UnaryOperation BinaryOperation.
From Maniunfold.Is Require Export
  Monoid Invertible Injective
  OneSortedUnaryAntidistributive
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

#[local] Instance is_cancel_l : IsCancelL _+_.
Proof.
  intros x y z a.
  rewrite <- (unl_bin_op_r x).
  rewrite <- (inv_r z).
  rewrite (assoc x z (- z)).
  setoid_rewrite a.
  rewrite <- (assoc y z (- z)).
  rewrite (inv_r z).
  rewrite (unl_bin_op_r y).
  reflexivity. Qed.

#[local] Instance is_cancel_r : IsCancelR _+_.
Proof.
  intros x y z a.
  rewrite <- (unl_bin_op_l x).
  rewrite <- (inv_l z).
  rewrite <- (assoc (- z) z x).
  setoid_rewrite a.
  rewrite (assoc (- z) z y).
  rewrite (inv_l z).
  rewrite (unl_bin_op_l y).
  reflexivity. Qed.

#[local] Instance is_cancel_l_r : IsCancelLR _+_.
Proof. split; typeclasses eauto. Qed.

#[local] Instance is_un_antidistr : IsUnAntidistr _+_ -_.
Proof.
  intros x y.
  apply (cancel_r (- (x + y)) ((- y) + (- x)) (x + y)).
  rewrite (inv_r (x + y)).
  rewrite (assoc (x + y) (- y) (- x)).
  rewrite <- (assoc x y (- y)).
  rewrite (inv_r y).
  rewrite (unl_bin_op_r x).
  rewrite (inv_r x).
  reflexivity. Qed.

#[local] Instance is_inj : IsInj -_.
Proof.
  intros x y a.
  rewrite <- (unl_bin_op_l y).
  rewrite <- (inv_r x).
  setoid_rewrite a.
  rewrite <- (assoc x (- y) y).
  rewrite (inv_l y).
  rewrite (unl_bin_op_r x).
  reflexivity. Qed.

#[local] Instance is_invol : IsInvol -_.
Proof.
  intros x.
  rewrite <- (unl_bin_op_r (- (- x))).
  rewrite <- (inv_l x).
  rewrite (assoc (- (- x)) (- x) x).
  rewrite (inv_l (- x)).
  rewrite (unl_bin_op_l x).
  reflexivity. Qed.

#[local] Instance is_un_absorb : IsUnAbsorb 0 -_.
Proof.
  hnf.
  rewrite <- (unl_bin_op_r (- 0)).
  rewrite (inv_l 0).
  reflexivity. Qed.

End Context.

#[export] Hint Resolve is_cancel_l is_cancel_r is_cancel_l_r is_un_antidistr
  is_inj is_invol is_un_absorb : typeclass_instances.
