(** * Group Structure *)

From DEZ.Has Require Export
  NullaryOperation UnaryOperation BinaryOperation.
From DEZ.Is Require Export
  Monoid Invertible
  Fixed Involutive Injective Cancellative Distributive.
From DEZ.ShouldHave Require Import
  AdditiveNotations.

(** ** Group *)

Class IsGrp (A : Type) (R : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) : Prop : Prop := {
  is_mon :> IsMon R x k;
  is_inv_l_r :> IsInvLR R x f k;
}.

Section Context.

Context (A : Type) `(IsGrp A).

#[local] Instance is_fixed : IsFixed 0 -_.
Proof.
  hnf.
  rewrite <- (unl_r (- 0)).
  setoid_rewrite (inv_l 0).
  reflexivity. Qed.

#[local] Instance is_invol : IsInvol -_.
Proof.
  intros x.
  rewrite <- (unl_r (- (- x))).
  setoid_rewrite <- (inv_l x).
  rewrite (assoc (- (- x)) (- x) x).
  rewrite (inv_l (- x)).
  rewrite (unl_l x).
  reflexivity. Qed.

#[local] Instance is_inj : IsInj -_.
Proof.
  intros x y a.
  rewrite <- (unl_l y).
  setoid_rewrite <- (inv_r x).
  setoid_rewrite a.
  rewrite <- (assoc x (- y) y).
  rewrite (inv_l y).
  rewrite (unl_r x).
  reflexivity. Qed.

#[local] Instance is_cancel_l : IsCancelL _+_.
Proof.
  intros x y z a.
  rewrite <- (unl_l x).
  setoid_rewrite <- (inv_l z).
  rewrite <- (assoc (- z) z x).
  setoid_rewrite a.
  rewrite (assoc (- z) z y).
  rewrite (inv_l z).
  rewrite (unl_l y).
  reflexivity. Qed.

#[local] Instance is_cancel_r : IsCancelR _+_.
Proof.
  intros x y z a.
  rewrite <- (unl_r x).
  setoid_rewrite <- (inv_r z).
  rewrite (assoc x z (- z)).
  setoid_rewrite a.
  rewrite <- (assoc y z (- z)).
  rewrite (inv_r z).
  rewrite (unl_r y).
  reflexivity. Qed.

#[local] Instance is_cancel_l_r : IsCancelLR _+_.
Proof. split; typeclasses eauto. Qed.

#[local] Instance is_antidistr : IsAntidistr -_ _+_ _+_.
Proof.
  intros x y.
  apply (cancel_l (- (x + y)) ((- y) + (- x)) (x + y)).
  rewrite (inv_r (x + y)).
  rewrite (assoc (x + y) (- y) (- x)).
  rewrite <- (assoc x y (- y)).
  rewrite (inv_r y).
  rewrite (unl_r x).
  rewrite (inv_r x).
  reflexivity. Qed.

End Context.

#[export] Hint Resolve is_fixed is_invol is_inj
  is_cancel_l is_cancel_r is_cancel_l_r is_antidistr : typeclass_instances.
