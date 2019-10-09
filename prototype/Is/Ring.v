From Maniunfold.Has Require Import EquivalenceRelation
  GroupOperation GroupIdentity GroupInverse
  FieldOperations FieldIdentities FieldInverses.
From Maniunfold.Is Require Import Semiring Identity Inverse Involutive
  Distributive Antidistributive Transitive Absorbing
  Setoid Semigroup Monoid Group AbelianGroup.

Class IsRing (A : Type) {has_eqv : HasEqv A}
  {has_add : HasAdd A} {has_zero : HasZero A} {has_neg : HasNeg A}
  {has_mul : HasMul A} {has_one : HasOne A} : Prop := {
  add_mul_is_semiring :> IsSemiring A;
  add_is_abelian_group :> IsAbelianGroup A
    (has_opr := has_add) (has_idn := has_zero) (has_inv := has_neg);
  mul_is_monoid :> IsMonoid A
    (has_opr := has_mul) (has_idn := has_one);
}.

Add Parametric Morphism {A : Type} `{is_ring : IsRing A} : neg
  with signature eqv ==> eqv
  as eqv_neg_morphism.
Proof.
  intros x y p.
  pose proof add_is_abelian_group as add_is_abelian_group.
  pose proof opr_is_group as add_is_group.
  pose proof inv_proper as neg_proper.
  apply neg_proper; auto. Qed.

(** TODO Find a way to avoid explicitly lifting these. *)

Theorem add_left_identity : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, 0 + x == x.
Proof.
  intros A ? ? ? ? ? ? ? x.
  pose proof add_is_abelian_group as add_is_abelian_group.
  pose proof opr_is_group as add_is_group.
  pose proof opr_is_monoid as add_is_monoid.
  pose proof opr_is_identity as add_is_identity.
  pose proof opr_is_left_identity as add_is_left_identity.
  apply opr_left_identity. Qed.

Theorem add_right_identity : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, x + 0 == x.
Proof.
  intros A ? ? ? ? ? ? ? x.
  pose proof add_is_abelian_group as add_is_abelian_group.
  pose proof opr_is_group as add_is_group.
  pose proof opr_is_monoid as add_is_monoid.
  pose proof opr_is_identity as add_is_identity.
  pose proof opr_is_right_identity as add_is_right_identity.
  apply opr_right_identity. Qed.

Theorem mul_left_identity : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, 1 * x == x.
Proof.
  intros A ? ? ? ? ? ? ? x.
  pose proof mul_is_monoid as mul_is_monoid.
  pose proof Monoid.opr_is_identity as mul_is_identity.
  pose proof opr_is_left_identity as mul_is_left_identity.
  apply opr_left_identity. Qed.

Theorem mul_right_identity : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, x * 1 == x.
Proof.
  intros A ? ? ? ? ? ? ? x.
  pose proof mul_is_monoid as mul_is_monoid.
  pose proof Monoid.opr_is_identity as mul_is_identity.
  pose proof opr_is_right_identity as mul_is_right_identity.
  apply opr_right_identity. Qed.

Theorem neg_involutive : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, - (- x) == x.
Proof.
  intros A ? ? ? ? ? ? ? x.
  pose proof add_is_abelian_group as add_is_abelian_group.
  pose proof opr_is_group as add_is_group.
  apply inv_involutive. Qed.

Instance neg_is_involutive {A : Type} `{is_ring : IsRing A} :
  IsInvolutive A := {}.
Proof. apply neg_involutive. Qed.

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

Theorem neg_add_antidistributive : forall {A : Type} `{is_ring : IsRing A},
  forall x y : A, - (x + y) == (- y) + (- x).
Proof.
  intros A ? ? ? ? ? ? ?.
  pose proof add_is_abelian_group as add_is_abelian_group.
  pose proof opr_is_group as add_is_group.
  apply inv_opr_antidistributive. Qed.

Instance neg_add_is_antidistributive {A : Type} `{is_ring : IsRing A} :
  IsAntidistributive A (has_opr := has_add) (has_inv := has_neg) := {}.
Proof. apply neg_add_antidistributive. Qed.

(** TODO Work out the rest. *)

Theorem zero_left_absorbing : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, 0 * x == 0.
Proof.
  intros A ? ? ? ? ? ? ? x.
  apply (add_right_injective (0 * x) 0 x).
  rewrite <- (mul_left_identity x) at 2.
  rewrite <- (mul_add_right_distributive 0 1 x).
  rewrite (add_left_identity 1). rewrite (add_left_identity x).
  rewrite (mul_left_identity x). reflexivity. Qed.

Theorem zero_right_absorbing : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, x * 0 == 0.
Proof.
  intros A ? ? ? ? ? ? ? x.
  apply (add_left_injective (x * 0) 0 x).
  rewrite <- (mul_right_identity x) at 1.
  rewrite <- (mul_add_left_distributive x 1 0).
  rewrite (add_right_identity 1). rewrite (add_right_identity x).
  rewrite (mul_right_identity x). reflexivity. Qed.

Instance zero_is_left_absorbing {A : Type} `{is_ring : IsRing A} :
  IsLeftAbsorbing A := {}.
Proof. apply zero_left_absorbing. Qed.

Instance zero_is_right_absorbing {A : Type} `{is_ring : IsRing A} :
  IsRightAbsorbing A := {}.
Proof. apply zero_right_absorbing. Qed.

Instance zero_is_absorbing {A : Type} `{is_ring : IsRing A} :
  IsAbsorbing A := {}.
