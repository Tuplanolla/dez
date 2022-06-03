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
  `{!IsRefl X} : IsRetr X id id.
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
  `{!IsRefl X} : IsSect X id id.
Proof. intros x. reflexivity. Qed.

End Context.

(** ** Retraction Map *)

Class IsRetrFn (A B : Type) (X : B -> B -> Prop) (f : A -> B) : Prop :=
  retr_fn_sect : exists g : B -> A, IsSect X f g.

(** ** Section Map *)

Class IsSectFn (A B : Type) (X : A -> A -> Prop) (f : A -> B) : Prop :=
  sect_fn_retr : exists g : B -> A, IsRetr X f g.

(** ** Retract *)

Class IsRetrType (A B : Type) (X : B -> B -> Prop) : Prop :=
  retr_type_retr_fn : exists f : A -> B, IsRetrFn X f.

Arguments IsRetrType _ _ _ : clear implicits.

(** ** Section *)

Class IsSectType (A B : Type) (X : A -> A -> Prop) : Prop :=
  sect_type_sect_fn : exists f : A -> B, IsSectFn X f.

Arguments IsSectType _ _ _ : clear implicits.

(** The term [IsRetr X f g] should be read
    as [g] being a retraction of [f] up to [X] and
    the term [IsSect X f g] should be read
    as [g] being a section of [f] up to [X].
    The term [IsRetrFn X f] should be read
    as [f] being a retraction up to [X] and
    the term [IsSectFn X f] should be read
    as [f] being a section up to [X].
    The term [IsRetrType A B X] should be read
    as [B] being a retract of [A] up to [X] and
    the term [IsSectType A B X] should be read
    as [B] being a section of [A] up to [X]. *)

Section Context.

Context (A B : Type) (X : A -> A -> Prop)
  (f : A -> B) (g : B -> A).

(** A retraction is a flipped section. *)

#[local] Instance retr_is_sect_flip
  `{!IsRetr X f g} : IsSect X g f.
Proof. auto. Qed.

(** A section is a flipped retraction. *)

#[local] Instance sect_is_retr_flip
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

Section Context.

Context (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) (g : B -> A).

#[local] Instance iso_l_is_iso_r_flip
  `{!IsIsoL X Y f g} : IsIsoR Y X g f.
Proof. esplit; eauto using retr_is_sect_flip with typeclass_instances. Qed.

#[local] Instance iso_r_is_iso_l_flip
  `{!IsIsoR Y X g f} : IsIsoL X Y f g.
Proof. esplit; eauto using sect_is_retr_flip with typeclass_instances. Qed.

End Context.

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

#[export] Instance refl_is_iso_l_id
  `{!IsRefl X} : IsIsoL X X id id.
Proof.
  split.
  - typeclasses eauto.
  - intros x. reflexivity. Qed.

#[export] Instance refl_is_iso_r_id
  `{!IsRefl X} : IsIsoR X X id id.
Proof.
  split.
  - typeclasses eauto.
  - intros x. reflexivity. Qed.

#[export] Instance refl_is_iso_id
  `{!IsRefl X} : IsIso X X id id.
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

Class IsCohIso (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) (g : B -> A)
  (Z : forall y : B, Y (f (g y)) y -> Y (f (g y)) y -> Prop) : Prop := {
  coh_iso_is_iso :> IsIso X Y f g;
  (* coh_iso_coh (x : A) :
    f_equal f (retr x) = sect (f x); *)
  coh_iso_coh (x : A) :
    Z _ (iso_l_is_proper (f := f) _ _ (retr x)) (sect (f x));
}.

(** ** Quasi-Inverse *)

Class IsQInv (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  q_inv_iso : exists g : B -> A, IsIso X Y f g.

Class IsLInv (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  l_inv_iso_l : exists g : B -> A, IsIsoL X Y f g.

Class IsRInv (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  r_inv_iso_r : exists g : B -> A, IsIsoR X Y f g.

(** ** Bi-Invertible Map *)

Class IsBiInv (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop := {
  bi_inv_is_l_inv :> IsLInv X Y f;
  bi_inv_is_r_inv :> IsRInv X Y f;
}.

(** ** Half-Adjoint Equivalence *)

Class IsHAE (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  h_a_e : exists g : B -> A, IsCohIso X Y f g (fun _ : B => _=_).

(** ** Contractible Map *)

Class IsContrMap (A B : Type)
  (f : A -> B) : Prop :=
  contr_map_is_contr_fn :> IsContrFn f.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** The identity function is a quasi-inverse
    with respect to any reflexive relation. *)

#[export] Instance refl_is_q_inv_id
  `{!IsRefl X} : IsQInv X X id.
Proof. exists id. typeclasses eauto. Qed.

(** The identity function is a bi-invertible map
    with respect to any reflexive relation. *)

#[export] Instance refl_is_bi_inv_id
  `{!IsRefl X} : IsBiInv X X id.
Proof.
  split.
  - exists id. typeclasses eauto.
  - exists id. typeclasses eauto. Qed.

#[local] Instance is_iso_eq_id :
  IsIso (A := A) (B := A) _=_ _=_ id id.
Proof.
  split.
  - split.
    + intros x y a. apply a.
    + intros x. apply id%type.
  - split.
    + intros x y a. apply a.
    + intros x. apply id%type. Defined.

(** The identity function is a half-adjoint equivalence. *)

#[export] Instance is_h_a_e_eq_id :
  IsHAE (A := A) (B := A) _=_ _=_ id.
Proof. exists id. exists is_iso_eq_id. intros x. reflexivity. Qed.

(** The identity function is a contractible map. *)

#[export] Instance is_contr_map_inv_eq_id :
  IsContrMap (A := A) (B := A) id.
Proof.
  intros y. unfold id, fib, IsContr. exists (exist (flip _=_ y) y id%type).
  intros [x a]. destruct a. reflexivity. Qed.

End Context.

(** ** Equivalent Types *)

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
  `{!IsRefl X} : IsEquivTypes A A X X.
Proof. exists id. typeclasses eauto. Qed.

End Context.
