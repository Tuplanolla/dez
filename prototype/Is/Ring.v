From Maniunfold.Has Require Import EquivalenceRelation
  GroupOperation GroupIdentity GroupInverse
  FieldOperations FieldIdentities FieldInverses.
From Maniunfold.Is Require Import Semiring Identifiable Invertible Involutive
  Distributive Antidistributive Transitive Absorbing
  Setoid Semigroup Monoid Group AbelianGroup.

Class IsRing (A : Type) {has_eqv : HasEqv A}
  {has_add : HasAdd A} {has_zero : HasZero A} {has_neg : HasNeg A}
  {has_mul : HasMul A} {has_one : HasOne A} : Prop := {
  add_mul_is_semiring :> IsSemiring A;
  add_is_abelian_group :> IsAbelianGroup A
    (has_opr := has_add) (has_idn := has_zero) (has_inv := has_neg);
  mul_is_monoid :> IsMonoid A (has_opr := has_mul) (has_idn := has_one);
}.

Instance ring_is_group {A : Type} `{is_ring : IsRing A} :
  IsGroup A (has_opr := has_add) (has_idn := has_zero) (has_inv := has_neg) :=
  opr_is_group.

Add Parametric Morphism {A : Type} `{is_ring : IsRing A} : neg
  with signature eqv ==> eqv
  as eqv_neg_morphism.
Proof.
  intros x y p.
  apply (inv_proper (has_opr := has_add)
    (has_idn := has_zero) (has_inv := has_neg)); auto. Qed.

(** TODO Clean up these projection chains. *)

Instance add_is_identifiable {A : Type} `{is_ring : IsRing A} :
  IsIdentifiable A (has_opr := has_add) (has_idn := has_zero) :=
  Monoid.opr_is_identifiable (IsMonoid := opr_is_monoid
    (IsGroup := opr_is_group (IsAbelianGroup := add_is_abelian_group))).

Instance add_is_left_identifiable {A : Type} `{is_ring : IsRing A} :
  IsLeftIdentifiable A (has_opr := has_add) (has_idn := has_zero) :=
  opr_is_left_identifiable (has_opr := has_add) (has_idn := has_zero).

Instance add_is_right_identifiable {A : Type} `{is_ring : IsRing A} :
  IsRightIdentifiable A (has_opr := has_add) (has_idn := has_zero) :=
  opr_is_right_identifiable (has_opr := has_add) (has_idn := has_zero).

Instance mul_is_identifiable {A : Type} `{is_ring : IsRing A} :
  IsIdentifiable A (has_opr := has_mul) (has_idn := has_one) :=
  Monoid.opr_is_identifiable (has_opr := has_mul) (has_idn := has_one).

Instance mul_is_left_identifiable {A : Type} `{is_ring : IsRing A} :
  IsLeftIdentifiable A (has_opr := has_mul) (has_idn := has_one) :=
  opr_is_left_identifiable (has_opr := has_mul) (has_idn := has_one).

Instance mul_is_right_identifiable {A : Type} `{is_ring : IsRing A} :
  IsRightIdentifiable A (has_opr := has_mul) (has_idn := has_one) :=
  opr_is_right_identifiable (has_opr := has_mul) (has_idn := has_one).

Instance neg_is_involutive {A : Type} `{is_ring : IsRing A} :
  IsInvolutive A (has_inv := has_neg) :=
  inv_is_involutive (is_group := opr_is_group
    (IsAbelianGroup := add_is_abelian_group)).

Lemma add_left_injective : forall {A : Type} `{is_ring : IsRing A},
  forall x y z : A, z + x == z + y -> x == y.
Proof.
  intros A ? ? ? ? ? ? ?.
  pose proof add_is_abelian_group as add_is_abelian_group.
  pose proof opr_is_group as add_is_group.
  apply opr_left_injective. Qed.

Lemma add_right_injective : forall {A : Type} `{is_ring : IsRing A},
  forall x y z : A, x + z == y + z -> x == y.
Proof.
  intros A ? ? ? ? ? ? ?.
  pose proof add_is_abelian_group as add_is_abelian_group.
  pose proof opr_is_group as add_is_group.
  apply opr_right_injective. Qed.

Instance neg_add_is_antidistributive {A : Type} `{is_ring : IsRing A} :
  IsAntidistributive A (has_opr := has_add) (has_inv := has_neg) :=
  inv_opr_is_antidistributive (is_group := opr_is_group
    (IsAbelianGroup := add_is_abelian_group)).

(** TODO Find a way to avoid explicitly lifting these. *)

Theorem add_left_identifiable : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, 0 + x == x.
Proof. intros A ? ? ? ? ? ? ?. apply add_is_left_identifiable. Qed.

Theorem add_right_identifiable : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, x + 0 == x.
Proof. intros A ? ? ? ? ? ? ?. apply add_is_right_identifiable. Qed.

Theorem mul_left_identifiable : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, 1 * x == x.
Proof. intros A ? ? ? ? ? ? ?. apply mul_is_left_identifiable. Qed.

Theorem mul_right_identifiable : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, x * 1 == x.
Proof. intros A ? ? ? ? ? ? ?. apply mul_is_right_identifiable. Qed.

Theorem neg_involutive : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, - (- x) == x.
Proof. intros A ? ? ? ? ? ? ?. apply neg_is_involutive. Qed.

(** TODO Work out the rest. *)

Theorem zero_left_absorbing : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, 0 * x == 0.
Proof.
  intros A ? ? ? ? ? ? ? x.
  apply (add_right_injective (0 * x) 0 x).
  rewrite <- (mul_left_identifiable x) at 2.
  rewrite <- (mul_add_right_distributive 0 1 x).
  rewrite (add_left_identifiable 1). rewrite (add_left_identifiable x).
  rewrite (mul_left_identifiable x). reflexivity. Qed.

Theorem zero_right_absorbing : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, x * 0 == 0.
Proof.
  intros A ? ? ? ? ? ? ? x.
  apply (add_left_injective (x * 0) 0 x).
  rewrite <- (mul_right_identifiable x) at 1.
  rewrite <- (mul_add_left_distributive x 1 0).
  rewrite (add_right_identifiable 1). rewrite (add_right_identifiable x).
  rewrite (mul_right_identifiable x). reflexivity. Qed.

Instance zero_is_left_absorbing {A : Type} `{is_ring : IsRing A} :
  IsLeftAbsorbing A := {}.
Proof. apply zero_left_absorbing. Qed.

Instance zero_is_right_absorbing {A : Type} `{is_ring : IsRing A} :
  IsRightAbsorbing A := {}.
Proof. apply zero_right_absorbing. Qed.

Instance zero_is_absorbing {A : Type} `{is_ring : IsRing A} :
  IsAbsorbing A := {}.
