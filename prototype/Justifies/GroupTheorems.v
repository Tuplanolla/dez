From Maniunfold.Has Require Import EquivalenceRelation
  GroupOperation GroupIdentity GroupInverse.
From Maniunfold.Is Require Import Associative LeftIdentity RightIdentity
  LeftInverse RightInverse Group.

Import AdditiveNotations.

(** TODO Move these into predicative classes. *)

Theorem inv_involutive : forall {A : Type} `{is_group : IsGroup A},
  forall x : A, - (- x) == x.
Proof.
  intros A ? ? ? ? ? x.
  rewrite <- (opr_right_identity (- (- x))). rewrite <- (opr_left_inverse x).
  rewrite (opr_associative (- (- x)) (- x) x).
  rewrite (opr_left_inverse (- x)). rewrite (opr_left_identity x).
  reflexivity. Qed.

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

Theorem opr_inv_distributive : forall {A : Type} `{is_group : IsGroup A},
  forall x y : A, - (x + y) == (- y) + (- x).
Proof.
  intros A ? ? ? ? ? x y.
  apply (opr_left_injective (- (x + y)) ((- y) + (- x)) (x + y)).
  rewrite (opr_right_inverse (x + y)).
  rewrite (opr_associative (x + y) (- y) (- x)).
  rewrite <- (opr_associative x y (- y)). rewrite (opr_right_inverse y).
  rewrite (opr_right_identity x). rewrite (opr_right_inverse x).
  reflexivity. Qed.

Theorem idn_inv_absorbing : forall {A : Type} `{is_group : IsGroup A},
  - 0 == 0.
Proof.
  intros A ? ? ? ? grp.
  rewrite <- (opr_right_identity (- 0)). rewrite (opr_left_inverse 0).
  reflexivity. Qed.
