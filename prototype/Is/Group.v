From Maniunfold.Has Require Import EquivalenceRelation
  GroupOperation GroupIdentity GroupInverse.
From Maniunfold.Is Require Import Associative Identity Inverse Involutive
  Antidistributive Setoid Monoid.

Import AdditiveNotations.

Class IsGroup (A : Type) {has_eqv : HasEqv A}
  {has_opr : HasOpr A} {has_idn : HasIdn A} {has_inv : HasInv A} : Prop := {
  inv_proper : inv ::> eqv ==> eqv;
  opr_is_monoid :> IsMonoid A;
  opr_is_inverse :> IsInverse A;
}.

Add Parametric Morphism {A : Type} `{is_group : IsGroup A} : inv
  with signature eqv ==> eqv
  as eqv_inv_morphism.
Proof. intros x y p. apply inv_proper; auto. Qed.

Theorem inv_involutive : forall {A : Type} `{is_group : IsGroup A},
  forall x : A, - (- x) == x.
Proof.
  intros A ? ? ? ? ? x.
  rewrite <- (opr_right_identity (- (- x))). rewrite <- (opr_left_inverse x).
  rewrite (opr_associative (- (- x)) (- x) x).
  rewrite (opr_left_inverse (- x)). rewrite (opr_left_identity x).
  reflexivity. Qed.

Instance inv_is_involutive {A : Type} `{is_group : IsGroup A} :
  IsInvolutive A := {}.
Proof. apply inv_involutive. Qed.

Lemma opr_left_injective : forall {A : Type} `{is_group : IsGroup A},
  forall x y z : A, z + x == z + y -> x == y.
Proof.
  intros A ? ? ? ? ? x y z p.
  rewrite <- (opr_left_identity x). rewrite <- (opr_left_inverse z).
  rewrite <- (opr_associative (- z) z x). rewrite p.
  rewrite (opr_associative (- z) z y). rewrite (opr_left_inverse z).
  rewrite (opr_left_identity y). reflexivity. Qed.

Lemma opr_right_injective : forall {A : Type} `{is_group : IsGroup A},
  forall x y z : A, x + z == y + z -> x == y.
Proof.
  intros A ? ? ? ? ? x y z p.
  rewrite <- (opr_right_identity x). rewrite <- (opr_right_inverse z).
  rewrite (opr_associative x z (- z)). rewrite p.
  rewrite <- (opr_associative y z (- z)). rewrite (opr_right_inverse z).
  rewrite (opr_right_identity y). reflexivity. Qed.

Theorem inv_opr_antidistributive : forall {A : Type} `{is_group : IsGroup A},
  forall x y : A, - (x + y) == (- y) + (- x).
Proof.
  intros A ? ? ? ? ? x y.
  apply (opr_left_injective (- (x + y)) ((- y) + (- x)) (x + y)).
  rewrite (opr_right_inverse (x + y)).
  rewrite (opr_associative (x + y) (- y) (- x)).
  rewrite <- (opr_associative x y (- y)). rewrite (opr_right_inverse y).
  rewrite (opr_right_identity x). rewrite (opr_right_inverse x).
  reflexivity. Qed.

Instance inv_opr_is_antidistributive {A : Type} `{is_group : IsGroup A} :
  IsAntidistributive A := {}.
Proof. apply inv_opr_antidistributive. Qed.

Theorem idn_inv : forall {A : Type} `{is_group : IsGroup A},
  - 0 == 0.
Proof.
  intros A ? ? ? ? grp.
  rewrite <- (opr_right_identity (- 0)). rewrite (opr_left_inverse 0).
  reflexivity. Qed.