(** * Left and Right Inverse or Section and Retraction of a Function and Isomorphism or Equivalence or Bijection *)

From DEZ Require Export
  Init.

Class IsIsoL (A B : Type) (f : A -> B) (g : B -> A) : Prop :=
  iso_l (a : A) : g (f a) = a.

Class IsIsoR (A B : Type) (f : A -> B) (g : B -> A) : Prop :=
  iso_r (b : B) : f (g b) = b.

Module RFromL.

Section Context.

Context (A B : Type) (f : A -> B) (g : B -> A) `(!IsIsoL f g).

(** A flipped left inverse is a right inverse. *)

#[local] Instance is_iso_r : IsIsoR g f.
Proof. auto. Qed.

End Context.

#[export] Hint Resolve is_iso_r : typeclass_instances.

End RFromL.

Module LFromR.

Section Context.

Context (A B : Type) (f : A -> B) (g : B -> A) `(!IsIsoR f g).

(** A flipped right inverse is a left inverse. *)

#[local] Instance is_iso_l : IsIsoL g f.
Proof. auto. Qed.

End Context.

#[export] Hint Resolve is_iso_l : typeclass_instances.

End LFromR.

(** We favor left isomorphisms and
    derive right ones from them automatically. *)

Export RFromL.

Class IsIsoLR (A B : Type) (f : A -> B) (g : B -> A) : Prop := {
  is_iso_l :> IsIsoL f g;
  is_iso_r :> IsIsoR f g;
}.

Module Flipped.

Section Context.

Context (A B : Type) (f : A -> B) (g : B -> A) `(!IsIsoLR f g).

(** A flipped isomorphism is an isomorphism. *)

#[local] Instance is_iso_l_r : IsIsoLR g f.
Proof.
  split.
  - intros b. apply iso_r.
  - intros a. apply iso_l. Qed.

End Context.

#[export] Hint Resolve is_iso_l_r : typeclass_instances.

End Flipped.

(** TODO Something in this vein. *)

From DEZ.Is Require Export
  Truncated.

Class IsEquiv (A B : Type) (f : A -> B) : Prop := {
  is_iso_l' : exists g : B -> A, IsIsoL f g;
  is_iso_r' : exists g : B -> A, IsIsoR f g;
}.

Class IsEquivType (A B : Type) : Prop :=
  equiv_type : exists f : A -> B, IsEquiv f.

(** True propositions are isomorphic to the unit type. *)

Lemma unit_is_equiv_type (A : Type) (x : A) `(IsProp A) : IsEquivType unit A.
Proof.
  exists (const x). split.
  - exists (const tt). intros []. reflexivity.
  - exists (const tt). intros y. unfold const. apply irrel. Qed.
