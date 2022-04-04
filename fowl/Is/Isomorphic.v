(** * Isomorphism *)

From DEZ Require Export
  Init.

(** ** Left Inverse of a Unary Function *)
(** ** Retraction of a Morphism *)

(** You should read [IsRetr f g] as [g] being a retraction of [f] and
    [IsSect f g] as [g] being a section of [f]. *)

Class IsRetr (A B : Type) (f : A -> B) (g : B -> A) : Prop :=
  retr (x : A) : g (f x) = x.

(** ** Right Inverse of a Unary Function *)
(** ** Section of a Morphism *)

Class IsSect (A B : Type) (f : A -> B) (g : B -> A) : Prop :=
  sect (x : B) : f (g x) = x.

Section Context.

Context (A B : Type) (f : A -> B) (g : B -> A).

(** A retraction is a flipped section. *)

#[export] Instance flip_retr_is_sect `{!IsRetr f g} : IsSect g f.
Proof. auto. Qed.

(** A section is a flipped retraction. *)

#[local] Instance flip_sect_is_retr `{!IsSect f g} : IsRetr g f.
Proof. auto. Qed.

End Context.

Class IsIso (A B : Type) (f : A -> B) (g : B -> A) : Prop := {
  iso_is_retr :> IsRetr f g;
  iso_is_sect :> IsSect f g;
}.

Section Context.

Context (A B : Type) (f : A -> B) (g : B -> A).

(** A flipped isomorphism is an isomorphism. *)

#[local] Instance flip_iso_is_iso `{!IsIso f g} : IsIso g f.
Proof.
  split.
  - intros x. apply sect.
  - intros x. apply retr. Qed.

End Context.
