(** * Unsquashing of Strict Propositions *)

From DEZ.Has Require Export
  Decisions.

(** ** Large Elimination *)
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

#[export] Instance notT_has_unsquash (A : Type)
  (f : - A) : HasUnsquash A.
Proof.
  intros xs.
  enough sEmpty by contradiction. induction xs as [x].
  contradiction. Defined.

(** Contradictory propositions can be unsquashed. *)

#[export] Instance not_has_unsquash (A : Prop)
  (f : ~ A) : HasUnsquash A.
Proof. apply notT_has_unsquash. auto. Defined.

(** Uninhabited types can be unsquashed. *)

#[export] Instance not_inhabited_has_unsquash (A : Type)
  (f : ~ inhabited A) : HasUnsquash A.
Proof. apply notT_has_unsquash. apply iff_notT_not_inhabited. auto. Defined.

(** The empty set can be unsquashed. *)

#[export] Instance has_unsquash_Empty_set : HasUnsquash Empty_set.
Proof. apply notT_has_unsquash. apply notT_Empty_set. Defined.

(** The false proposition can be unsquashed. *)

#[export] Instance has_unsquash_False : HasUnsquash 0.
Proof. apply notT_has_unsquash. apply not_False. Defined.

(** Dependent functions with unsquashable codomains can be unsquashed. *)

#[export] Instance has_unsquash_forall (A : Type) (P : A -> Type)
  {u : forall x : A, HasUnsquash (P x)} : HasUnsquash (forall x : A, P x).
Proof.
  intros fs x.
  apply unsquash. induction fs as [f]. apply squash.
  auto. Defined.

(** Functions with unsquashable codomains can be unsquashed. *)

#[local] Instance has_unsquash_fun (A B : Type)
  {u : HasUnsquash B} : HasUnsquash (A -> B).
Proof. apply has_unsquash_forall. Defined.

(** Negations can be unsquashed. *)

#[local] Instance has_unsquash_not (A : Prop) : HasUnsquash (~ A).
Proof. apply has_unsquash_forall. Defined.

(** Decidable propositions can be unsquashed. *)

#[export] Instance dec_has_unsquash (A : Prop)
  {d : HasDec A} : HasUnsquash A.
Proof.
  intros xs. decide A as [x | f].
  - auto.
  - apply notT_has_unsquash.
    + auto.
    + auto. Defined.
