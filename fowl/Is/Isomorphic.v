(** * Isomorphisms and Equivalences *)

From DEZ.Is Require Export
  Commutative Contractible Proper Reflexive.

(** ** Retraction *)
(** ** Unary Function with a Left Inverse *)

Class IsRetr (A B : Type) (X : A -> A -> Prop)
  (f : A -> B) (g : B -> A) : Prop :=
  retr (x : A) : X (g (f x)) x.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** The identity function is a retraction of itself
    with respect to any reflexive relation. *)

#[export] Instance refl_is_retr_id
  `{!IsRefl X} : IsRetr X id id | 100.
Proof. intros x. reflexivity. Qed.

End Context.

(** ** Section *)
(** ** Unary Function with a Right Inverse *)

Class IsSect (A B : Type) (X : B -> B -> Prop)
  (f : A -> B) (g : B -> A) : Prop :=
  sect (y : B) : X (f (g y)) y.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** The identity function is a section of itself
    with respect to any reflexive relation. *)

#[export] Instance refl_is_sect_id
  `{!IsRefl X} : IsSect X id id | 100.
Proof. intros x. reflexivity. Qed.

End Context.

(** The term [IsRetr f g] should be read
    as [g] being a retraction of [f] and
    the term [IsSect f g] should be read
    as [g] being a section of [f]. *)

Section Context.

Context (A B : Type) (X : A -> A -> Prop)
  (f : A -> B) (g : B -> A).

(** A retraction is a flipped section. *)

#[local] Instance flip_retr_is_sect
  `{!IsRetr X f g} : IsSect X g f.
Proof. auto. Qed.

(** A section is a flipped retraction. *)

#[local] Instance flip_sect_is_retr
  `{!IsSect X g f} : IsRetr X f g.
Proof. auto. Qed.

End Context.

Class IsIsoL (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) (g : B -> A) : Prop := {
  iso_l_is_proper :> IsProper (X ==> Y) f;
  iso_l_is_retr :> IsRetr X f g;
}.

Class IsIsoR (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) (g : B -> A) : Prop := {
  iso_r_is_proper :> IsProper (Y ==> X) g;
  iso_r_is_sect :> IsSect Y f g;
}.

(** ** Isomorphism *)

Class IsIso (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) (g : B -> A) : Prop := {
  iso_is_iso_l :> IsIsoL X Y f g;
  iso_is_iso_r :> IsIsoR X Y f g;
}.

Section Context.

Context (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) (g : B -> A).

(** A flipped isomorphism is an isomorphism. *)

#[local] Instance flip_iso_is_iso
  `{!IsIso X Y f g} : IsIso Y X g f.
Proof.
  split.
  - split.
    + typeclasses eauto.
    + intros x. apply sect.
  - split.
    + typeclasses eauto.
    + intros x. apply retr. Qed.

End Context.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** The identity function is an isomorphism
    with respect to any reflexive relation. *)

#[export] Instance refl_is_iso_id
  `{!IsRefl X} : IsIso X X id id | 100.
Proof.
  split.
  - split.
    + typeclasses eauto.
    + intros x. reflexivity.
  - split.
    + typeclasses eauto.
    + intros x. reflexivity. Qed.

End Context.

(** ** Automorphism *)
(** ** Unary Operation with a Two-Sided Inverse *)

Class IsAuto (A : Type) (X : A -> A -> Prop)
  (f g : A -> A) : Prop := {
  auto_is_iso_l :> IsIsoL X X f g;
  auto_is_iso_r :> IsIsoR X X f g;
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

Class IsCohIso (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop) (f : A -> B) (g : B -> A)
  (Z : forall y : B, Y (f (g y)) y -> Y (f (g y)) y -> Prop) : Prop := {
  coh_iso_is_iso :> IsIso X Y f g;
  (* coh_iso_coh : forall x : A,
    f_equal f (retr x) = sect (f x); *)
  coh_iso_coh : forall x : A,
    Z _ (iso_l_is_proper (f := f) _ _ (retr x)) (sect (f x));
}.

(** ** Quasi-Inverse *)

Class IsQInv (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  q_inv_iso : exists g : B -> A, IsIso X Y f g.

(** ** Half-Adjoint Equivalence *)

Class IsHAE (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop) (f : A -> B) : Prop :=
  h_a_e : exists g : B -> A, IsCohIso X Y f g (fun _ : B => _=_).

(** ** Bi-Invertible Map *)

Class IsBiInv (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop) (f : A -> B) : Prop := {
  bi_inv_iso_l : exists g : B -> A, IsIsoL X Y f g;
  bi_inv_iso_r : exists h : B -> A, IsIsoR X Y f h;
}.

(** ** Contractible Map *)

Class IsContrMap (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop) (f : A -> B) : Prop := {
  contr_map_is_proper :> IsProper (X ==> Y) f;
  contr_map_is_contr_fn :> IsContrFn Y f;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** The identity function is an equivalence
    with respect to any reflexive relation. *)

#[export] Instance refl_is_bi_inv_id
  `{!IsRefl X} : IsBiInv X X id | 100.
Proof.
  split.
  - exists id. typeclasses eauto.
  - exists id. typeclasses eauto. Qed.

End Context.

(** ** Equivalent Types *)

Class IsEquivTypes' (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop) : Prop :=
  equiv_types_h_a_e : exists f : A -> B, IsHAE X Y f.

Arguments IsEquivTypes' _ _ _ _ : clear implicits.
Arguments equiv_types_h_a_e _ _ _ _ {_}.

Class IsEquivTypes (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop) : Prop :=
  equiv_types_bi_inv : exists f : A -> B, IsBiInv X Y f.

Arguments IsEquivTypes _ _ _ _ : clear implicits.
Arguments equiv_types_bi_inv _ _ _ _ {_}.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** A type is equivalent to itself
    with respect to any reflexive relation. *)

#[export] Instance refl_is_equiv_types
  `{!IsRefl X} : IsEquivTypes A A X X | 100.
Proof. exists id. typeclasses eauto. Qed.

End Context.
