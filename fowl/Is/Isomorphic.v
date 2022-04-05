(** * Isomorphisms *)

From DEZ Require Export
  Init.
From DEZ.Is Require Export
  Equivalence.

(** The definition [IsRetr f g] should be read
    as [g] being a retraction of [f] and
    the definition [IsSect f g] should be read
    as [g] being a section of [f]. *)

(** ** Left Inverse of a Unary Function *)
(** ** Retraction of a Morphism *)

Class IsRetr (A B : Type) (X : A -> A -> Prop)
  (f : A -> B) (g : B -> A) : Prop :=
  retr (x : A) : X (g (f x)) x.

(** ** Right Inverse of a Unary Function *)
(** ** Section of a Morphism *)

Class IsSect (A B : Type) (X : B -> B -> Prop)
  (f : A -> B) (g : B -> A) : Prop :=
  sect (x : B) : X (f (g x)) x.

Section Context.

Context (A B : Type) (X : A -> A -> Prop)
  (f : A -> B) (g : B -> A).

(** A retraction is a flipped section. *)

#[export] Instance flip_retr_is_sect `{!IsRetr X f g} : IsSect X g f.
Proof. auto. Qed.

(** A section is a flipped retraction. *)

#[local] Instance flip_sect_is_retr `{!IsSect X g f} : IsRetr X f g.
Proof. auto. Qed.

End Context.

(** ** Inverse of a Unary Function *)
(** ** Isomorphism *)

Class IsIso (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) (g : B -> A) : Prop := {
  iso_dom_is_equiv : IsEquiv X;
  iso_codom_is_equiv : IsEquiv Y;
  iso_is_retr :> IsRetr X f g;
  iso_is_sect :> IsSect Y f g;
}.

Section Context.

Context (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) (g : B -> A) `{!IsEquiv X} `{!IsEquiv Y}.

(** A flipped isomorphism is an isomorphism. *)

#[local] Instance flip_iso_is_iso `{!IsIso X Y f g} : IsIso Y X g f.
Proof.
  split.
  - typeclasses eauto.
  - typeclasses eauto.
  - intros x. apply sect.
  - intros x. apply retr. Qed.

End Context.

(** ** Bijective Unary Function *)
(** ** Isomorphic Mapping *)

Class IsBij (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  bij_is_iso : exists g : B -> A, IsIso X Y f g.

(** ** Convertible Types *)
(** ** Isomorphic Types *)

Class IsConv (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop) : Prop :=
  conv_is_bij : exists (f : A -> B), IsBij X Y f.
