(** * Isomorphisms *)

From DEZ.Is Require Export
  Proper Reflexive.

(** The term [IsRetr f g] should be read
    as [g] being a retraction of [f] and
    the term [IsSect f g] should be read
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

#[export] Instance flip_retr_is_sect
  `{!IsRetr X f g} : IsSect X g f.
Proof. auto. Qed.

(** A section is a flipped retraction. *)

#[local] Instance flip_sect_is_retr
  `{!IsSect X g f} : IsRetr X f g.
Proof. auto. Qed.

End Context.

(** ** Inverse of a Unary Function *)
(** ** Isomorphism *)

Class IsIso (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) (g : B -> A) : Prop := {
  iso_sect_is_proper :> IsProper (X ==> Y) f;
  iso_retr_is_proper :> IsProper (Y ==> X) g;
  iso_is_retr :> IsRetr X f g;
  iso_is_sect :> IsSect Y f g;
}.

Section Context.

Context (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) (g : B -> A).

(** A flipped isomorphism is an isomorphism. *)

#[local] Instance flip_iso_is_iso
  `{!IsIso X Y f g} : IsIso Y X g f.
Proof.
  split.
  - typeclasses eauto.
  - typeclasses eauto.
  - intros x. apply sect.
  - intros x. apply retr. Qed.

End Context.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** The identity function is an isomorphism
    with respect to any reflexive relation. *)

#[export] Instance refl_is_iso_id
  `{!IsRefl X} : IsIso X X id id | 100.
Proof.
  split.
  - typeclasses eauto.
  - typeclasses eauto.
  - intros x. reflexivity.
  - intros x. reflexivity. Qed.

End Context.

(** ** Automorphism *)
(** ** Inverse of a Unary Operation *)

Class IsAuto (A : Type) (X : A -> A -> Prop)
  (f g : A -> A) : Prop := {
  auto_sect_is_proper :> IsProper (X ==> X) f;
  auto_retr_is_proper :> IsProper (X ==> X) g;
  auto_is_retr :> IsRetr X f g;
  auto_is_sect :> IsSect X f g;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (f g : A -> A).

(** An automorphism is a special case of an isomorphism. *)

#[export] Instance auto_is_iso
  `{!IsAuto X f g} : IsIso X X f g.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance iso_is_auto
  `{!IsIso X X f g} : IsAuto X f g.
Proof. esplit; typeclasses eauto. Qed.

End Context.

(** ** Equivalent Types *)
(** ** Isomorphic Types *)

Class IsEquivTypes (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop) : Prop :=
  equiv_types : exists (f : A -> B) (g : B -> A), IsIso X Y f g.

Arguments IsEquivTypes _ _ _ _ : clear implicits.
Arguments equiv_types _ _ _ _ {_}.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** A type is equivalent to itself
    with respect to any reflexive relation. *)

#[export] Instance refl_is_equiv_types
  `{!IsRefl X} : IsEquivTypes A A X X | 100.
Proof. exists id, id. typeclasses eauto. Qed.

End Context.
