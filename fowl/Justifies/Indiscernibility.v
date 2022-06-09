(** * Indiscernibility *)

From DEZ.Has Require Export
  Operations Distances EquivalenceRelations.
From DEZ.Supports Require Import
  AdditiveNotations EquivalenceNotations.

Lemma eq_indisc (A : Type) (P : A -> Prop)
  (x y : A) (a : x = y) : P x <-> P y.
Proof. rewrite a. reflexivity. Qed.

Lemma indisc_eq (A : Type)
  (x y : A) (a : forall P : A -> Prop, P x <-> P y) : x = y.
Proof. apply a. reflexivity. Qed.

(** ** Identity of Indiscernibles *)
(** ** Leibniz's Law *)

Theorem iff_eq_indisc (A : Type) (x y : A) :
  x = y <-> forall P : A -> Prop, P x <-> P y.
Proof.
  split.
  - intros a P. auto using eq_indisc.
  - intros a. auto using indisc_eq.
Qed.
