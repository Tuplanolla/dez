(** * Isomorphisms and Equivalences *)

From DEZ.Is Require Export
  Commutative Contractible Proper Reflexive.
From DEZ.Is Require Export
  Equivalence.

(** ** Retraction *)
(** ** Unary Function with a Left Inverse *)

Class IsRetr (A B : Type) (X : A -> A -> Prop)
  (f : A -> B) (g : B -> A) : Prop :=
  retr (x : A) : X (g (f x)) x.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** The identity function is a retraction of itself
    with respect to any reflexive relation. *)

#[local] Instance refl_is_retr_id
  `{!IsRefl X} : IsRetr X id id.
Proof. intros x. reflexivity. Defined.

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

#[local] Instance refl_is_sect_id
  `{!IsRefl X} : IsSect X id id.
Proof. intros x. reflexivity. Defined.

End Context.

(** ** Retraction Map *)

Class IsRetrFn (A B : Type) (Y : B -> B -> Prop) (f : A -> B) : Type :=
  retr_fn_sect : {g : B -> A | IsSect Y f g}.

(** ** Section Map *)

Class IsSectFn (A B : Type) (X : A -> A -> Prop) (f : A -> B) : Type :=
  sect_fn_retr : {g : B -> A | IsRetr X f g}.

(** ** Retract *)

Class IsRetrType (A B : Type) (Y : B -> B -> Prop) : Type :=
  retr_type_retr_fn : {f : A -> B & IsRetrFn Y f}.

Arguments IsRetrType _ _ _ : clear implicits.

(** ** Sect *)

Class IsSectType (A B : Type) (X : A -> A -> Prop) : Type :=
  sect_type_sect_fn : {f : A -> B & IsSectFn X f}.

Arguments IsSectType _ _ _ : clear implicits.

(** The term [IsRetr X f g] should be read
    as [g] being a retraction of [f] up to [X] and
    the term [IsSect X f g] should be read
    as [g] being a section of [f] up to [X].
    The term [IsRetrFn Y f] should be read
    as [f] being a retraction up to [Y] and
    the term [IsSectFn X f] should be read
    as [f] being a section up to [X].
    The term [IsRetrType A B Y] should be read
    as [B] being a retract of [A] up to [Y] and
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
  iso_l_is_proper_f :> IsProper (X ==> Y) f;
  iso_l_is_proper_g :> IsProper (Y ==> X) g;
  iso_l_is_retr :> IsRetr X f g;
}.

Class IsIsoR (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) (g : B -> A) : Prop := {
  iso_r_is_proper_f :> IsProper (X ==> Y) f;
  iso_r_is_proper_g :> IsProper (Y ==> X) g;
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
    + typeclasses eauto.
    + intros x. apply sect.
  - split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros x. apply retr.
Qed.

End Context.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** The identity function is an isomorphism
    with respect to any reflexive relation. *)

#[local] Instance refl_is_iso_l_id
  `{!IsRefl X} : IsIsoL X X id id.
Proof.
  split.
  - typeclasses eauto.
  - typeclasses eauto.
  - intros x. reflexivity.
Qed.

#[local] Instance refl_is_iso_r_id
  `{!IsRefl X} : IsIsoR X X id id.
Proof.
  split.
  - typeclasses eauto.
  - typeclasses eauto.
  - intros x. reflexivity.
Qed.

#[local] Instance refl_is_iso_id
  `{!IsRefl X} : IsIso X X id id.
Proof.
  split.
  - split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros x. reflexivity.
  - split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros x. reflexivity.
Qed.

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

(** ** Quasi-Inverse *)

Class IsQInv (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Type :=
  q_inv_iso : {g : B -> A | IsIso X Y f g}.

Class IsLInv (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  l_inv_iso_l' : exists g : B -> A, IsIsoL X Y f g.

(** TODO Investigate the effects of this change. *)

Class HasLInv (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Type :=
  l_inv : {g : B -> A | IsIsoL X Y f g}.

Section Context.

Context (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B).

#[export] Instance l_inv_is_l_inv
  `{!HasLInv X Y f} : IsLInv X Y f.
Proof. destruct l_inv as [g IIL]. exists g. typeclasses eauto. Qed.

End Context.

Class IsRInv (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Type :=
  r_inv_iso_r : {g : B -> A | IsIsoR X Y f g}.

(** ** Bi-Invertible Map *)

Class IsBiInv (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Type := {
  bi_inv_has_l_inv :> HasLInv X Y f;
  bi_inv_is_r_inv :> IsRInv X Y f;
}.

Section Context.

Context (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B).

(** A quasi-inverse is a bi-invertible map. *)

#[export] Instance q_inv_is_bi_inv
  `{!IsQInv X Y f} : IsBiInv X Y f.
Proof.
  split.
  - destruct q_inv_iso as [g II]. exists g. typeclasses eauto.
  - destruct q_inv_iso as [g II]. exists g. typeclasses eauto.
Qed.

(** A bi-invertible map is a quasi-inverse. *)

#[local] Instance bi_inv_is_q_inv
  `{!IsEquiv X} `{!IsEquiv Y} `{!IsBiInv X Y f} : IsQInv X Y f.
Proof.
  destruct l_inv as [g IIL]. destruct r_inv_iso_r as [h IIR].
  exists (g o f o h). split.
  - split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros x. unfold compose. rewrite sect. rewrite retr. reflexivity.
  - split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros x. unfold compose. rewrite retr. rewrite sect. reflexivity.
Qed.

End Context.

(** ** Contractible Map *)

Class IsContrMap (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Type := {
  contr_map_is_proper :> IsProper (X ==> Y) f;
  contr_map_is_contr_fn :> IsContrFn X Y f;
}.

Class IsCohIso (A B : Type)
  (f : A -> B) (g : B -> A) : Prop := {
  coh_iso_is_iso :> IsIso _=_ _=_ f g;
  coh_iso_coh (x : A) : @f_equal A B f (g (f x)) x (retr x) = sect (f x);
  (** This would make an adjoint equivalence! *)
  (*
  coh_iso_is_iso :> IsIso X Y f g;
  coh_iso_coh (x : A) : iso_l_is_proper_f (f := f) _ _ (retr x) = sect (f x);
  coh_iso_coh' (y : B) : iso_r_is_proper_g (g := g) _ _ (sect y) = retr (g y);
  *)
}.

(** ** Half-Adjoint Equivalence *)

Class IsHAE (A B : Type)
  (f : A -> B) : Type :=
  h_a_e : {g : B -> A | IsCohIso f g}.

Section Context.

#[local] Existing Instance refl_is_iso_id.

Context (A : Type) (X : A -> A -> Prop).

(** The identity function is a quasi-inverse
    with respect to any reflexive relation. *)

#[local] Instance refl_is_q_inv_id
  `{!IsRefl X} : IsQInv X X id.
Proof. exists id. typeclasses eauto. Qed.

(** The identity function is a bi-invertible map
    with respect to any reflexive relation. *)

#[local] Instance refl_is_bi_inv_id
  `{!IsRefl X} : IsBiInv X X id.
Proof.
  split.
  - exists id. typeclasses eauto.
  - exists id. typeclasses eauto.
Qed.

(** The identity function is a contractible map
    with respect to any reflexive relation. *)

#[local] Instance refl_is_contr_map_inv_id
  `{!IsRefl X} : IsContrMap X X id.
Proof.
  split.
  - typeclasses eauto.
  - intros y. exists (y; refl y)%sig. intros [x a]. apply a.
Qed.

#[local] Instance is_iso_eq_id :
  IsIso (A := A) (B := A) _=_ _=_ id id.
Proof.
  split.
  - split.
    + intros x y a. apply a.
    + intros x y a. apply a.
    + intros x. apply id%type.
  - split.
    + intros x y a. apply a.
    + intros x y a. apply a.
    + intros x. apply id%type.
Defined.

(** The identity function is a half-adjoint equivalence. *)

#[export] Instance is_h_a_e_eq_id :
  IsHAE (A := A) (B := A) id.
Proof. exists id. exists is_iso_eq_id. intros x. reflexivity. Qed.
  (*
  exists id. pose is_iso_eq_id as II. exists II.
  subst II.
  unfold iso_l_is_proper_f. unfold iso_is_iso_l. unfold is_iso_eq_id.
  intros x. reflexivity.
  *)

End Context.

Class IsCorrRel (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop) (R : A -> B -> Prop) : Type := {
  corr_rel_is_iso :> IsProper (X ==> Y ==> _<->_) R;
  corr_rel_contr_A (x : A) :> IsContr {y : B | R x y} (proj1_sig_relation Y);
  corr_rel_contr_B (y : B) :> IsContr {x : A | R x y} (proj1_sig_relation X);
}.

(** ** One-to-One Correspondence of Types *)

Class IsCorrTypes (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop) : Type :=
  corr_types : {R : A -> B -> Prop & IsCorrRel X Y R}.

Arguments IsCorrTypes _ _ _ _ : clear implicits.
Arguments corr_types _ _ _ _ {_}.

Equations corr_fn (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop)
  `{!IsCorrTypes A B X Y} (x : A) : B :=
  corr_fn x := _.
Next Obligation.
  intros A B X Y [R [IP f g]] x.
  destruct (f x) as [[y r] a].
  apply y.
Defined.

Equations corr_inv_fn (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop)
  `{!IsCorrTypes A B X Y} (y : B) : A :=
  corr_inv_fn x := _.
Next Obligation.
  intros A B X Y [R [IP f g]] y.
  destruct (g y) as [[x r] a].
  apply x.
Defined.

(** ** Equivalent Types *)

Class IsEquivTypes (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop) : Type :=
  equiv_types_bi_inv : {f : A -> B & IsBiInv X Y f}.

Arguments IsEquivTypes _ _ _ _ : clear implicits.
Arguments equiv_types_bi_inv _ _ _ _ {_}.

Equations equiv_fn (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop)
  `{!IsEquivTypes A B X Y} (x : A) : B :=
  equiv_fn x := _.
Next Obligation.
  intros A B X Y [f IBI] x.
  apply (f x).
Defined.

Equations equiv_inv_fn (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop)
  `{!IsEquivTypes A B X Y} (y : B) : A :=
  equiv_inv_fn x := _.
Next Obligation.
  intros A B X Y [f [[g IIL] IRI]] y.
  apply (g y).
Defined.

(** An equivalence of types is an equivalence relation. *)

Section Context.

Context (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop)
  `{!IsEquiv X} `{!IsEquiv Y}.

#[local] Instance corr_types_is_equiv_types
  `{!IsCorrTypes A B X Y} : IsEquivTypes A B X Y.
Proof.
  match goal with
  | x : IsCorrTypes _ _ _ _ |- _ => rename x into ICT
  end.
  destruct ICT as [R [pro f g]].
  assert (h : forall (uh oh : _) (eh : X uh oh) (no : _), R uh no -> R oh no).
  intros. eapply pro; eauto. symmetry. apply eh. reflexivity.
  assert (h' : forall (uh oh : _) (eh : Y uh oh) (no : _), R no uh -> R no oh).
  intros. eapply pro; eauto. reflexivity. symmetry. apply eh.
  exists (fun x : A => proj1_sig (proj1_sig (f x))).
  split.
  - exists (fun y : B => proj1_sig (proj1_sig (g y))).
    split.
    + intros x y e.
      destruct (f x) as [[b r] p].
      destruct (f y) as [[a s] q].
      unfold proj1_sig.
      pose proof h y x (sym _ _ e) a s as w.
      pose proof h x y e b r as u.
      specialize (p (a; w)%sig).
      specialize (q (b; u)%sig).
      cbn in p, q.
      apply (sym _ _) in q.
      apply p || apply q.
    + intros x y e.
      destruct (g x) as [[b r] p].
      destruct (g y) as [[a s] q].
      unfold proj1_sig.
      pose proof h' y x (sym _ _ e) a s as w.
      pose proof h' x y e b r as u.
      specialize (p (a; w)%sig).
      specialize (q (b; u)%sig).
      cbn in p, q.
      apply (sym _ _) in q.
      apply p || apply q.
    + intros x.
      destruct (f x) as [[b r] p].
      unfold proj1_sig.
      destruct (g b) as [[a s] q].
      specialize (q (x; r)%sig).
      cbn in p, q.
      apply q.
  - exists (fun y : B => proj1_sig (proj1_sig (g y))).
    split.
    + intros x y e.
      destruct (f x) as [[b r] p].
      destruct (f y) as [[a s] q].
      unfold proj1_sig.
      pose proof h y x (sym _ _ e) a s as w.
      pose proof h x y e b r as u.
      specialize (p (a; w)%sig).
      specialize (q (b; u)%sig).
      cbn in p, q.
      apply (sym _ _) in q.
      apply p || apply q.
    + intros x y e.
      destruct (g x) as [[b r] p].
      destruct (g y) as [[a s] q].
      unfold proj1_sig.
      pose proof h' y x (sym _ _ e) a s as w.
      pose proof h' x y e b r as u.
      specialize (p (a; w)%sig).
      specialize (q (b; u)%sig).
      cbn in p, q.
      apply (sym _ _) in q.
      apply p || apply q.
    + intros y.
      destruct (g y) as [[a s] q].
      unfold proj1_sig.
      destruct (f a) as [[b r] p].
      specialize (p (y; s)%sig).
      cbn in p, q.
      apply p.
Defined.

#[local] Instance equiv_types_is_corr_types
  `{!IsEquivTypes A B X Y} : IsCorrTypes A B X Y.
Proof.
  match goal with
  | x : IsEquivTypes _ _ _ _ |- _ => rename x into IET
  end.
  destruct IET as [f [[g [p q r]] [h [_ q' s]]]].
  set (R (x : A) (y : B) := X (g y) x /\ Y (f x) y).
  hnf. exists R. split.
  - intros x y a x' y' a'. unfold R. split.
    + intros [b b']; split.
      * rewrite a in *. rewrite a' in *. apply b.
      * rewrite a in *. rewrite a' in *. apply b'.
    + intros [b b']; split.
      * rewrite a in *. rewrite a' in *. apply b.
      * rewrite a in *. rewrite a' in *. apply b'.
  - intros x. hnf. eexists (f x; _)%sig. intros [y r']. cbn.
    subst R. cbn in r'. destruct r' as [r'0 r'1]. apply r'1.
  - intros y. hnf. eexists (g (f (h y)); _)%sig. intros [x r']. cbn.
    subst R. cbn in r'. destruct r' as [r'0 r'1]. rewrite sect. apply r'0.
Unshelve.
    cbn. subst R. cbn. split. rewrite retr. reflexivity. reflexivity.
    cbn. subst R. cbn. split. rewrite sect. reflexivity. rewrite retr. rewrite sect. reflexivity.
Defined.

End Context.

(** An equivalence of types is an equivalence relation. *)

Section Context.

Context (A B C : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop) (Z : C -> C -> Prop)
  `{!IsEquiv X} `{!IsEquiv Y} `{!IsEquiv Z}.

#[local] Instance refl_is_equiv_types :
  IsEquivTypes A A X X.
Proof.
  exists id. split.
  - exists id. split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros x. reflexivity.
  - exists id. split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros x. reflexivity.
Qed.

#[local] Instance sym_is_equiv_types
  `{!IsEquivTypes A B X Y} : IsEquivTypes B A Y X.
Proof.
  pose proof _ : IsEquivTypes A B X Y as e.
  destruct e as [f [[g IIL] [h IIR]]].
  exists (g o f o h). split.
  - exists f. split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros y. unfold compose.
      rewrite retr. rewrite sect. reflexivity.
  - exists f. split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros x. unfold compose.
      rewrite sect. rewrite retr. reflexivity.
Qed.

#[local] Instance trans_is_equiv_types
  `{!IsEquivTypes A B X Y} `{!IsEquivTypes B C Y Z} : IsEquivTypes A C X Z.
Proof.
  pose proof _ : IsEquivTypes A B X Y as IETAB.
  pose proof _ : IsEquivTypes B C Y Z as IETBC.
  destruct IETAB as [f [[g IILf] [h IIRf]]], IETBC as [i [[j IILi] [k IIRi]]].
  exists (i o f). split.
  - exists (g o j). split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros y. unfold compose.
      rewrite retr. rewrite retr. reflexivity.
  - exists (h o k). split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros y. unfold compose.
      rewrite sect. rewrite sect. reflexivity.
Qed.

End Context.

(** TODO See if higher relations win you anything over plain equality. *)

(** ** Equivalent Types up to Equality *)

Class IsEquivTypesEq (X : forall A : Type, A -> A -> Prop) (A B : Type) : Prop :=
  equiv_types_eq_is_equiv_types :> inhabited (IsEquivTypes A B (X A) (X B)).

(** An equivalence of types is an equivalence relation. *)

Section Context.

Context (X : forall A : Type, A -> A -> Prop)
  `{!forall A : Type, IsEquiv (X A)}.

Arguments X _ _ _ : clear implicits.

#[local] Instance is_refl_equiv_types_eq :
  IsRefl (IsEquivTypesEq X).
Proof. intros A. constructor. apply refl_is_equiv_types. Qed.

#[local] Instance is_sym_equiv_types_eq :
  IsSym (IsEquivTypesEq X).
Proof. intros A B [IET]. constructor. apply sym_is_equiv_types. Qed.

#[local] Instance is_trans_equiv_types_eq :
  IsTrans (IsEquivTypesEq X).
Proof. intros A B C [IETAB] [IETBC]. constructor. apply trans_is_equiv_types. Qed.

End Context.
