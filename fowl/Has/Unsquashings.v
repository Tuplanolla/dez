(** * Unsquashing *)

From DEZ.Has Require Export
  Decisions.

(** ** Large Elimination for Strict Propositions *)
(** ** Unsquashing *)

Class HasUnsquash (A : Type) : Type := unsquash (x : Squash A) : A.

#[export] Typeclasses Transparent HasUnsquash.

Lemma notT_Empty_set : - Empty_set.
Proof. intros x. contradiction. Qed.

Lemma not_False : ~ 0.
Proof. intros x. contradiction. Qed.

Lemma iff_notT_not_inhabited (A : Type) : - A <-> ~ inhabited A.
Proof.
  split.
  - intros f xs. induction xs as [x]. contradiction.
  - intros f x. apply inhabits in x. contradiction. Qed.

(** Unconstrucible types can be unsquashed. *)

#[local] Instance notT_type_has_unsquash (A : Type)
  (f : - A) : HasUnsquash A.
Proof.
  intros xs. enough sEmpty by contradiction. induction xs as [x].
  contradiction. Qed.

(** Contradictory propositions can be unsquashed. *)

#[export] Instance not_prop_has_unsquash (A : Prop)
  (f : ~ A) : HasUnsquash A.
Proof. apply notT_type_has_unsquash. auto. Qed.

(** Uninhabited types can be unsquashed. *)

#[export] Instance not_inhabited_has_unsquash (A : Type)
  (f : ~ inhabited A) : HasUnsquash A.
Proof. apply notT_type_has_unsquash. apply iff_notT_not_inhabited. auto. Qed.

(** The empty set can be unsquashed. *)

#[export] Instance Empty_set_has_unsquash : HasUnsquash Empty_set.
Proof. apply notT_type_has_unsquash. apply notT_Empty_set. Qed.

(** The false proposition can be unsquashed. *)

#[export] Instance False_has_unsquash : HasUnsquash False.
Proof. apply notT_type_has_unsquash. apply not_False. Qed.

(** Dependent functions with unsquashable codomains can be unsquashed. *)

#[export] Instance forall_has_unsquash (A : Type) (P : A -> Type)
  {u : forall x : A, HasUnsquash (P x)} : HasUnsquash (forall x : A, P x).
Proof.
  intros fs x. apply unsquash. induction fs as [f]. apply squash. auto. Qed.

(** Functions with unsquashable codomains can be unsquashed. *)

#[local] Instance fun_has_unsquash (A B : Type)
  {u : HasUnsquash B} : HasUnsquash (A -> B).
Proof. apply forall_has_unsquash. Qed.

(** Negations can be unsquashed. *)

#[local] Instance not_has_unsquash (A : Prop) : HasUnsquash (~ A).
Proof. apply forall_has_unsquash. Qed.

(** Decidable propositions can be unsquashed. *)

#[export] Instance dec_has_unsquash (A : Prop)
  {d : HasDec A} : HasUnsquash A.
Proof.
  intros xs. decide A as [x | f].
  - auto.
  - apply notT_type_has_unsquash.
    + auto.
    + auto. Qed.
