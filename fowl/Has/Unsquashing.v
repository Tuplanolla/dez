(** * Unsquashing or Large Elimination for Strict Propositions *)

From DEZ.Has Require Export
  Decisions.

Class HasUnsquash (A : Type) : Type := unsquash (x : Squash A) : A.

Typeclasses Transparent HasUnsquash.

Section Context.

(** Empty types can be unsquashed. *)

#[local] Instance Empty_set_has_unsquash : HasUnsquash Empty_set.
Proof.
  intros x.
  enough sEmpty by contradiction.
  inversion x as [f].
  contradiction. Qed.

(** False propositions can be unsquashed.
    This is a special case of [Empty_set_has_unsquash]. *)

#[local] Instance False_has_unsquash : HasUnsquash False.
Proof.
  intros x.
  enough sEmpty by contradiction.
  inversion x as [f].
  contradiction. Qed.

(** Dependent functions with unsquashable codomains can be unsquashed. *)

#[local] Instance pi_has_unsquash (A : Type) (P : A -> Type)
  (u : forall a : A, HasUnsquash (P a)) : HasUnsquash (forall a : A, P a).
Proof.
  intros x a.
  apply unsquash.
  inversion x as [f].
  apply squash.
  auto. Qed.

(** Functions with unsquashable codomains can be unsquashed.
    This is a special case of [pi_has_unsquash]. *)

#[local] Instance arrow_has_unsquash (A B : Type)
  (Hu : HasUnsquash B) : HasUnsquash (A -> B).
Proof.
  intros x a.
  apply unsquash.
  inversion x as [f].
  apply squash.
  auto. Qed.

(** Negations can be unsquashed.
    This is a special case of [False_has_unsquash] and [arrow_has_unsquash]. *)

#[local] Instance notT_has_unsquash (A : Type) : HasUnsquash (- A).
Proof.
  intros x a.
  enough sEmpty by contradiction.
  inversion x as [f].
  contradiction. Qed.

(** This is a special case of [pi_has_unsquash]. *)

#[local] Instance not_has_unsquash (A : Prop) : HasUnsquash (~ A).
Proof.
  intros x a.
  enough sEmpty by contradiction.
  inversion x as [f].
  contradiction. Qed.

(** Decidable propositions can be unsquashed. *)

#[local] Instance dec_has_unsquash (A : Prop)
  (Hd : HasDec A) : HasUnsquash A.
Proof.
  intros x.
  decide A as [a | f].
  - auto.
  - enough sEmpty by contradiction.
    inversion x as [a].
    contradiction. Qed.

End Context.

#[export] Hint Resolve Empty_set_has_unsquash False_has_unsquash
  notT_has_unsquash not_has_unsquash
  pi_has_unsquash arrow_has_unsquash
  dec_has_unsquash : typeclass_instances.
