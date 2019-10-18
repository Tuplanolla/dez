From Maniunfold.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities FieldInverses.
From Maniunfold.Is Require Export
  Semiring AbelianGroup Monoid.
From Maniunfold.Is Require Import
  Involutive Antidistributive LeftAbsorbing RightAbsorbing Absorbing.

Class IsRing {A : Type} {has_eqv : HasEqv A}
  (has_add : HasAdd A) (has_zero : HasZero A) (has_neg : HasNeg A)
  (has_mul : HasMul A) (has_one : HasOne A) : Prop := {
  ring_is_semiring :> IsSemiring add zero mul one;
  ring_add_is_abelian_group :> IsAbelianGroup add zero neg;
  ring_mul_is_monoid :> IsMonoid mul one;
}.

Section Context.

Context {A : Type} `{is_ring : IsRing A}.

(** The following specializations help type inference. *)

Corollary add_associative : forall x y z : A, x + (y + z) == (x + y) + z.
Proof. apply associative. Qed.

Corollary add_left_identifiable : forall x : A, 0 + x == x.
Proof. apply left_identifiable. Qed.

Corollary add_right_identifiable : forall x : A, x + 0 == x.
Proof. apply right_identifiable. Qed.

Corollary add_left_invertible : forall x : A, (- x) + x == 0.
Proof. apply left_invertible. Qed.

Corollary add_right_invertible : forall x : A, x + (- x) == 0.
Proof. apply right_invertible. Qed.

Corollary add_commutative : forall x y : A, x + y == y + x.
Proof. apply commutative. Qed.

Corollary mul_associative : forall x y z : A, x * (y * z) == (x * y) * z.
Proof. apply associative. Qed.

Corollary mul_left_identifiable : forall x : A, 1 * x == x.
Proof. apply left_identifiable. Qed.

Corollary mul_right_identifiable : forall x : A, x * 1 == x.
Proof. apply right_identifiable. Qed.

Corollary zero_neg : - 0 == 0.
Proof. apply idn_inv. Qed.

Corollary add_left_injective : forall x y z : A, z + x == z + y -> x == y.
Proof. apply left_injective. Qed.

Corollary add_right_injective : forall x y z : A, x + z == y + z -> x == y.
Proof. apply right_injective. Qed.

Corollary neg_involutive : forall x : A, - (- x) == x.
Proof. apply involutive. Qed.

Corollary neg_add_antidistributive : forall x y : A,
  - (x + y) == (- y) + (- x).
Proof. apply antidistributive. Qed.

Theorem zero_left_absorbing : forall x : A, 0 * x == 0.
Proof.
  intros x.
  apply (add_right_injective (0 * x) 0 x).
  rewrite <- (mul_left_identifiable x) at 2.
  rewrite <- (right_distributive 0 1 x).
  rewrite (add_left_identifiable 1).
  rewrite (mul_left_identifiable x).
  rewrite (add_left_identifiable x).
  reflexivity. Qed.

Global Instance : IsLeftAbsorbing mul zero := {}.
Proof. apply zero_left_absorbing. Qed.

Theorem zero_right_absorbing : forall x : A, x * 0 == 0.
Proof.
  intros x.
  apply (add_left_injective (x * 0) 0 x).
  rewrite <- (mul_right_identifiable x) at 1.
  rewrite <- (left_distributive x 1 0).
  rewrite (add_right_identifiable 1).
  rewrite (mul_right_identifiable x).
  rewrite (add_right_identifiable x).
  reflexivity. Qed.

Global Instance : IsRightAbsorbing mul zero := {}.
Proof. apply zero_right_absorbing. Qed.

Global Instance : IsAbsorbing mul zero := {}.

Theorem iff_ring_trivial : 1 == 0 <-> forall x : A, x == 0.
Proof.
  split.
  - intros H x. rewrite <- (mul_left_identifiable x). rewrite H.
    rewrite (zero_left_absorbing x). reflexivity.
  - intros H. apply H. Qed.

End Context.
