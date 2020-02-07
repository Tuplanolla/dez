From Maniunfold.Has Require Export
  EquivalenceRelation Addition Negation Multiplication.
From Maniunfold.Is Require Export
  Commutative Group Monoid Distributive Absorbing BinaryCommutative Semiring.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

Class IsRing {A : Type} {has_eq_rel : HasEqRel A}
  (has_add : HasAdd A) (has_zero : HasZero A) (has_neg : HasNeg A)
  (has_mul : HasMul A) (has_one : HasOne A) : Prop := {
  add_is_comm :> IsComm add;
  add_zero_neg_is_grp :> IsGrp add zero neg;
  add_mul_is_distr :> IsDistr add mul;
  mul_one_is_mon :> IsMon mul one;
}.

(** TODO Where do these belong? *)

Ltac change_add_grp :=
  change_add_mon;
  change un_op with neg.

Section Context.

Context {A : Type} `{is_ring : IsRing A}.

Theorem zero_mul_l_absorb : forall x : A,
  0 * x == 0.
Proof with change_add_grp || change_mul_mon.
  intros x.
  apply (l_cancel (0 * x) 0 (1 * x))...
  rewrite (r_unl (1 * x))...
  rewrite <- (r_distr 1 0 x)...
  rewrite (r_unl 1)...
  reflexivity. Qed.

Global Instance zero_mul_is_l_absorb : IsLAbsorb zero mul.
Proof. intros x. apply zero_mul_l_absorb. Qed.

Theorem zero_mul_r_absorb : forall x : A,
  x * 0 == 0.
Proof with change_add_grp || change_mul_mon.
  intros x.
  apply (l_cancel (x * 0) 0 (x * 1))...
  rewrite (r_unl (x * 1))...
  rewrite <- (l_distr x 1 0)...
  rewrite (r_unl 1)...
  reflexivity. Qed.

Global Instance zero_mul_is_r_absorb : IsRAbsorb zero mul.
Proof. intros x. apply zero_mul_r_absorb. Qed.

Global Instance zero_mul_is_absorb : IsAbsorb zero mul.
Proof. constructor; typeclasses eauto. Qed.

(** TODO What are these theorems? *)

Theorem l_wtf : forall x : A,
  - (1) * x == - x.
Proof with change_add_grp || change_mul_mon.
  intros x.
  apply (l_cancel (- (1) * x) (- x) x)...
  rewrite (r_inv x)...
  rewrite <- (l_unl x) at 1...
  rewrite <- (r_distr 1 (- (1)) x)...
  rewrite (r_inv 1)...
  rewrite (l_absorb x)...
  reflexivity. Qed.

Fail Global Instance neg_mul_is_l_wtf : IsLWtf neg mul.

Theorem r_wtf : forall x : A,
  x * - (1) == - x.
Proof with change_add_grp || change_mul_mon.
  intros x.
  apply (l_cancel (x * - (1)) (- x) x)...
  rewrite (r_inv x)...
  rewrite <- (r_unl x) at 1...
  rewrite <- (l_distr x)...
  rewrite (r_inv 1)...
  rewrite (r_absorb x)...
  reflexivity. Qed.

Fail Global Instance neg_mul_is_r_wtf : IsRWtf neg mul.

(* Global Instance neg_mul_is_wtf : IsWtf neg mul.
Proof. constructor; typeclasses eauto. Qed. *)

Theorem neg_mul_l_bin_comm : forall x y : A,
  - (x * y) == - x * y.
Proof with change_add_grp || change_mul_mon.
  intros x y.
  rewrite <- (l_wtf (x * y)).
  rewrite (assoc (- (1)) x y)...
  rewrite l_wtf.
  reflexivity. Qed.

Global Instance neg_mul_is_l_bin_comm : IsLBinComm neg mul.
Proof. intros x y. apply neg_mul_l_bin_comm. Qed.

Theorem neg_mul_r_bin_comm : forall x y : A,
  - (x * y) == x * - y.
Proof with change_add_grp || change_mul_mon.
  intros x y.
  rewrite <- (r_wtf (x * y)).
  rewrite <- (assoc x y (- (1)))...
  rewrite r_wtf.
  reflexivity. Qed.

Global Instance neg_mul_is_r_bin_comm : IsRBinComm neg mul.
Proof. intros x y. apply neg_mul_r_bin_comm. Qed.

Global Instance neg_mul_is_bin_comm : IsBinComm neg mul.
Proof. constructor; typeclasses eauto. Qed.

Goal 0 == 1 -> forall x y : A, x == y.
Proof with change_add_grp || change_mul_mon.
  intros H x y.
  rewrite <- (l_unl x)...
  rewrite <- (l_unl y)...
  rewrite <- H.
  rewrite (l_absorb x)...
  rewrite (l_absorb y)...
  reflexivity. Qed.

Global Instance add_zero_mul_one_is_sring : IsSring add zero mul one.
Proof. constructor; typeclasses eauto. Qed.

End Context.
