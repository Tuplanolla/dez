(** * Group Structure *)

From DEZ.Has Require Export
  EquivalenceRelation NullaryOperation UnaryOperation BinaryOperation.
From DEZ.Is Require Export
  Monoid Invertible Proper
  Fixed Involutive Injective Cancellative Distributive.
From DEZ.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

(** ** Group *)

Class IsGrp (A : Type) (R : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) : Prop := {
  is_mon :> IsMon R x k;
  is_inv_l_r :> IsInvLR R x f k;
  is_proper :> IsProper (R ==> R) f;
}.

Section Context.

(** TODO We can use notations if we declare things as follows. *)

Context (A : Type) (R : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A)
  `(!IsGrp R x f k).

#[local] Instance has_eq_rel : HasEqRel A := R.
#[local] Instance has_null_op : HasNullOp A := x.
#[local] Instance has_un_op : HasUnOp A := f.
#[local] Instance has_bin_op : HasBinOp A := k.

Ltac notate :=
  change R with _==_ in *;
  change x with 0 in *;
  change f with -_ in *;
  change k with _+_ in *.

#[local] Instance is_fixed : IsFixed R x f.
Proof.
  hnf.
  setoid_rewrite <- (unl_r (f x)).
  setoid_rewrite (inv_l x).
  reflexivity. Qed.

#[local] Instance is_invol : IsInvol R f.
Proof.
  notate.
  intros y.
  setoid_rewrite <- (unl_r (- (- y))).
  setoid_rewrite <- (inv_l y).
  setoid_rewrite (assoc (- (- y)) (- y) y).
  setoid_rewrite (inv_l (- y)).
  setoid_rewrite (unl_l y).
  reflexivity. Qed.

#[local] Instance is_inj : IsInj R R f.
Proof.
  notate.
  intros y z a.
  setoid_rewrite <- (unl_l z).
  setoid_rewrite <- (inv_r y).
  setoid_rewrite a.
  setoid_rewrite <- (assoc y (- z) z).
  setoid_rewrite (inv_l z).
  setoid_rewrite (unl_r y).
  reflexivity. Qed.

#[local] Instance is_cancel_l : IsCancelL R k.
Proof.
  notate.
  intros y z w a.
  setoid_rewrite <- (unl_l y).
  setoid_rewrite <- (inv_l w).
  setoid_rewrite <- (assoc (- w) w y).
  setoid_rewrite a.
  setoid_rewrite (assoc (- w) w z).
  setoid_rewrite (inv_l w).
  setoid_rewrite (unl_l z).
  reflexivity. Qed.

#[local] Instance is_cancel_r : IsCancelR R k.
Proof.
  notate.
  intros y z w a.
  setoid_rewrite <- (unl_r y).
  setoid_rewrite <- (inv_r w).
  setoid_rewrite (assoc y w (- w)).
  setoid_rewrite a.
  setoid_rewrite <- (assoc z w (- w)).
  setoid_rewrite (inv_r w).
  setoid_rewrite (unl_r z).
  reflexivity. Qed.

#[local] Instance is_cancel_l_r : IsCancelLR R k.
Proof. split; typeclasses eauto. Qed.

#[local] Instance is_antidistr : IsAntidistr R f k k.
Proof.
  notate.
  intros y z.
  apply (cancel_l (- (y + z)) ((- z) + (- y)) (y + z)).
  setoid_rewrite (inv_r (y + z)).
  setoid_rewrite (assoc (y + z) (- z) (- y)).
  setoid_rewrite <- (assoc y z (- z)).
  setoid_rewrite (inv_r z).
  setoid_rewrite (unl_r y).
  setoid_rewrite (inv_r y).
  reflexivity. Qed.

End Context.

#[export] Hint Resolve is_fixed is_invol is_inj
  is_cancel_l is_cancel_r is_cancel_l_r is_antidistr : typeclass_instances.
