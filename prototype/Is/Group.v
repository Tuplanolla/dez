From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity GroupInverse.
From Maniunfold.Is Require Export
  Monoid Invertible.
From Maniunfold.Is Require Import
  Involutive Antidistributive.

Import AdditiveNotations.

Class IsGroup (A : Type) {has_eqv : HasEqv A}
  {has_opr : HasOpr A} {has_idn : HasIdn A} {has_inv : HasInv A} : Prop := {
  inv_proper :> IsProper (eqv ==> eqv) inv;
  opr_is_monoid :> IsMonoid A;
  opr_is_invertible :> IsInvertible A;
}.

Add Parametric Morphism {A : Type} `{is_group : IsGroup A} : inv
  with signature eqv ==> eqv
  as eqv_inv_morphism.
Proof. intros x y p. apply inv_proper; auto. Qed.

Lemma idn_inv : forall {A : Type} `{is_group : IsGroup A},
  - 0 == 0.
Proof.
  intros A ? ? ? ? ?.
  rewrite <- (opr_right_identifiable (- 0)).
  rewrite (opr_left_invertible 0).
  reflexivity. Qed.

Lemma opr_left_injective : forall {A : Type} `{is_group : IsGroup A},
  forall x y z : A, z + x == z + y -> x == y.
Proof.
  intros A ? ? ? ? ? x y z p.
  rewrite <- (opr_left_identifiable x).
  rewrite <- (opr_left_invertible z).
  rewrite <- (opr_associative (- z) z x).
  rewrite p.
  rewrite (opr_associative (- z) z y).
  rewrite (opr_left_invertible z).
  rewrite (opr_left_identifiable y).
  reflexivity. Qed.

Lemma opr_right_injective : forall {A : Type} `{is_group : IsGroup A},
  forall x y z : A, x + z == y + z -> x == y.
Proof.
  intros A ? ? ? ? ? x y z p.
  rewrite <- (opr_right_identifiable x).
  rewrite <- (opr_right_invertible z).
  rewrite (opr_associative x z (- z)).
  rewrite p.
  rewrite <- (opr_associative y z (- z)).
  rewrite (opr_right_invertible z).
  rewrite (opr_right_identifiable y).
  reflexivity. Qed.

Theorem inv_involutive : forall {A : Type} `{is_group : IsGroup A},
  forall x : A, - (- x) == x.
Proof.
  intros A ? ? ? ? ? x.
  rewrite <- (opr_right_identifiable (- (- x))).
  rewrite <- (opr_left_invertible x).
  rewrite (opr_associative (- (- x)) (- x) x).
  rewrite (opr_left_invertible (- x)).
  rewrite (opr_left_identifiable x).
  reflexivity. Qed.

Instance inv_is_involutive {A : Type} `{is_group : IsGroup A} :
  IsInvolutive A := {}.
Proof. apply inv_involutive. Qed.

Theorem inv_opr_antidistributive : forall {A : Type} `{is_group : IsGroup A},
  forall x y : A, - (x + y) == (- y) + (- x).
Proof.
  intros A ? ? ? ? ? x y.
  apply (opr_left_injective (- (x + y)) ((- y) + (- x)) (x + y)).
  rewrite (opr_right_invertible (x + y)).
  rewrite (opr_associative (x + y) (- y) (- x)).
  rewrite <- (opr_associative x y (- y)).
  rewrite (opr_right_invertible y).
  rewrite (opr_right_identifiable x).
  rewrite (opr_right_invertible x).
  reflexivity. Qed.

Instance inv_opr_is_antidistributive {A : Type} `{is_group : IsGroup A} :
  IsAntidistributive A := {}.
Proof. apply inv_opr_antidistributive. Qed.
