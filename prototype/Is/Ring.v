From Maniunfold.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities FieldInverses.
From Maniunfold.Is Require Export
  Semiring AbelianGroup Monoid.
From Maniunfold.Is Require Import
  Involutive Antidistributive LeftAbsorbing RightAbsorbing Absorbing.

Class IsRing (A : Type) {has_eqv : HasEqv A}
  {has_add : HasAdd A} {has_zero : HasZero A} {has_neg : HasNeg A}
  {has_mul : HasMul A} {has_one : HasOne A} : Prop := {
  ring_is_semiring :> IsSemiring A;
  ring_add_is_abelian_group :> IsAbelianGroup A
    (has_opr := has_add) (has_idn := has_zero) (has_inv := has_neg);
  ring_mul_is_monoid :> IsMonoid A (has_opr := has_mul) (has_idn := has_one);
}.

Add Parametric Morphism {A : Type} `{is_ring : IsRing A} : neg
  with signature eqv ==> eqv
  as eqv_neg_morphism.
Proof. intros x y p. apply group_inv_is_proper; auto. Qed.

(** The following specializations help type inference. *)

Corollary add_associative : forall {A : Type} `{is_ring : IsRing A},
  forall x y z : A, x + (y + z) == (x + y) + z.
Proof. intros A ? ? ? ? ? ? ?. apply associative. Qed.

Corollary add_left_identifiable : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, 0 + x == x.
Proof. intros A ? ? ? ? ? ? ?. apply left_identifiable. Qed.

Corollary add_right_identifiable : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, x + 0 == x.
Proof. intros A ? ? ? ? ? ? ?. apply right_identifiable. Qed.

Corollary add_left_invertible : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, (- x) + x == 0.
Proof. intros A ? ? ? ? ? ? ?. apply left_invertible. Qed.

Corollary add_right_invertible : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, x + (- x) == 0.
Proof. intros A ? ? ? ? ? ? ?. apply right_invertible. Qed.

Corollary add_commutative : forall {A : Type} `{is_ring : IsRing A},
  forall x y : A, x + y == y + x.
Proof. intros A ? ? ? ? ? ? ?. apply commutative. Qed.

Corollary mul_associative : forall {A : Type} `{is_ring : IsRing A},
  forall x y z : A, x * (y * z) == (x * y) * z.
Proof. intros A ? ? ? ? ? ? ?. apply associative. Qed.

Corollary mul_left_identifiable : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, 1 * x == x.
Proof. intros A ? ? ? ? ? ? ?. apply left_identifiable. Qed.

Corollary mul_right_identifiable : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, x * 1 == x.
Proof. intros A ? ? ? ? ? ? ?. apply right_identifiable. Qed.

Corollary zero_neg : forall {A : Type} `{is_ring : IsRing A},
  - 0 == 0.
Proof. intros A ? ? ? ? ? ? ?. apply idn_inv. Qed.

Corollary add_left_injective : forall {A : Type} `{is_ring : IsRing A},
  forall x y z : A, z + x == z + y -> x == y.
Proof. intros A ? ? ? ? ? ? ?. apply left_injective. Qed.

Corollary add_right_injective : forall {A : Type} `{is_ring : IsRing A},
  forall x y z : A, x + z == y + z -> x == y.
Proof. intros A ? ? ? ? ? ? ?. apply right_injective. Qed.

Corollary neg_involutive : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, - (- x) == x.
Proof. intros A ? ? ? ? ? ? ?. apply involutive. Qed.

Corollary neg_add_antidistributive : forall {A : Type} `{is_ring : IsRing A},
  forall x y : A, - (x + y) == (- y) + (- x).
Proof. intros A ? ? ? ? ? ? ?. apply antidistributive. Qed.

Theorem zero_left_absorbing : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, 0 * x == 0.
Proof.
  intros A ? ? ? ? ? ? ? x.
  apply (add_right_injective (0 * x) 0 x).
  rewrite <- (mul_left_identifiable x) at 2.
  rewrite <- (right_distributive 0 1 x).
  rewrite (add_left_identifiable 1).
  rewrite (mul_left_identifiable x).
  rewrite (add_left_identifiable x).
  reflexivity. Qed.

Instance zero_is_left_absorbing {A : Type} `{is_ring : IsRing A} :
  IsLeftAbsorbing A := {}.
Proof. apply zero_left_absorbing. Qed.

Theorem zero_right_absorbing : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, x * 0 == 0.
Proof.
  intros A ? ? ? ? ? ? ? x.
  apply (add_left_injective (x * 0) 0 x).
  rewrite <- (mul_right_identifiable x) at 1.
  rewrite <- (left_distributive x 1 0).
  rewrite (add_right_identifiable 1).
  rewrite (mul_right_identifiable x).
  rewrite (add_right_identifiable x).
  reflexivity. Qed.

Instance zero_is_right_absorbing {A : Type} `{is_ring : IsRing A} :
  IsRightAbsorbing A := {}.
Proof. apply zero_right_absorbing. Qed.

Instance zero_is_absorbing {A : Type} `{is_ring : IsRing A} :
  IsAbsorbing A := {}.

Theorem iff_ring_trivial : forall {A : Type} `{is_ring : IsRing A},
  1 == 0 <-> forall x : A, x == 0.
Proof.
  intros A ? ? ? ? ? ? ?. split.
  - intros H x. rewrite <- (mul_left_identifiable x). rewrite H.
    rewrite (zero_left_absorbing x). reflexivity.
  - intros H. apply H. Qed.
