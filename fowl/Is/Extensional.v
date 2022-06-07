(** * Extensionality and Univalence *)

From Coq Require Import
  Logic.FunctionalExtensionality Logic.ProofIrrelevance
  Logic.PropExtensionality Logic.PropExtensionalityFacts.
From DEZ.Is Require Export
  Irrelevant Isomorphic.

(** We declare various axiom schemes as classes
    in hopes of one day turning them into theorems. *)

Theorem ac : forall {A B : Type} (R : A -> B -> Prop),
  (forall x : A, {y : B | R x y}) -> {f : A -> B | forall x : A, R x (f x)}.
Proof.
  intros A B R g. exists (fun x : A => proj1_sig (g x)).
  intros x. set (p := g x). induction p as [y p]. cbn. apply p.
Defined.

Theorem dpb : forall {A B : Type} (R : A -> B -> Prop),
  {f : A -> B | forall x : A, R x (f x)} -> forall x : A, {y : B | R x y}.
Proof.
  intros A B R p x. induction p as [f g]. exists (f x). apply (g x).
Defined.

(** This is lemma 2.15.6 from the book. *)

Theorem ac_eq (A : Type) (P : A -> Type) (R : forall x : A, P x -> Prop)
  (f : forall x : A, {a : P x | R x a}) :
  {g : forall x : A, P x | forall x : A, R x (g x)}.
Proof.
  exists (fun x : A => proj1_sig (f x)). intros x. set (f x) as y.
  destruct y as [a s]. apply s.
Defined.

(** This is part of theorem 2.15.7 from the book. *)

Theorem dbp_eq (A : Type) (P : A -> Type) (R : forall x : A, P x -> Prop)
  (s : {g : forall x : A, P x | forall x : A, R x (g x)}) (x : A) :
  {a : P x | R x a}.
Proof.
  destruct s as [g f]. exists (g x). apply (f x).
Defined.

(** TODO Clean up this mess. *)

Reserved Notation "x '_*'" (left associativity, at level 20).
Reserved Notation "x '~=' y" (no associativity, at level 70).

Definition transport (A : Type) (P : A -> Type)
  (x y : A) (e : x = y) (a : P x) : P y.
Proof.
  induction e. apply a.
Defined.

#[local] Notation "'_*_'" := (transport _) (only parsing).
#[local] Notation "e '_*'" := (transport _ e) (only parsing).

Lemma happly_nondep (A B : Type) (f g : A -> B) (e : f = g) (x : A) : f x = g x.
Proof.
  apply (transport (fun h : A -> B => f x = h x) e). apply id%type.
Defined.

Lemma happly (A : Type) (P : A -> Type)
  (f g : forall x : A, P x) (e : f = g) (x : A) : f x = g x.
Proof.
  apply (transport (fun h : forall x : A, P x => f x = h x) e). apply id%type.
Defined.

#[local] Notation "'_~=_'" := (fun A B : Type => IsEquivTypes A B _=_ _=_).
#[local] Notation "A '~=' B" := (IsEquivTypes A B _=_ _=_).

(** This is lemma 2.3.9 from the book. *)

Definition transport_trans (A : Type) (P : A -> Type)
  (x y z : A) (e : x = y) (f : y = z) (a : P x) :
  f _* (e _* a) = (f o e)%type _* a.
Proof.
  destruct e, f. apply id%type.
Defined.

(** This is part of theorem 2.15.7 from the book. *)

Theorem do_not_need_this (A : Type) (P : A -> Type) (R : forall x : A, P x -> Prop) :
  IsLInv _=_ _=_ (@ac_eq A P R).
Proof.
  exists (@dbp_eq A P R). split.
  - typeclasses eauto.
  - typeclasses eauto.
  - intros f. apply functional_extensionality_dep.
    intros x. destruct (f x) as [a s] eqn : e. cbn. rewrite e. reflexivity.
Defined.

Theorem need_this (A : Type) (P : A -> Type) (R : forall x : A, P x -> Prop) :
  IsRInv _=_ _=_ (@ac_eq A P R).
Proof.
  exists (@dbp_eq A P R). split.
  - typeclasses eauto.
  - typeclasses eauto.
  - intros [g f]. reflexivity.
Defined.

(** This is theorem 2.15.7 from the book. *)

Theorem this_is_equiv (A : Type) (P : A -> Type) (R : forall x : A, P x -> Prop) :
  IsBiInv _=_ _=_ (@ac_eq A P R).
Proof.
  split.
  - apply do_not_need_this.
  - apply need_this.
Defined.

Theorem seriously (A : Type) (P : A -> Type) (R : forall x : A, P x -> Prop) :
  (forall x : A, {a : P x | R x a}) ~=
  {g : forall x : A, P x | forall x : A, R x (g x)}.
Proof. exists ac_eq. apply this_is_equiv. Defined.

(** We define these instances as explicitly as possible,
    because they are used in the univalence axiom. *)

(** ** Properties of Equality *)

#[export] Instance is_proper_eq_0 (B : Type) (x : B) :
  IsProper _=_ x.
Proof. apply id%type. Defined.

#[export] Instance is_proper_eq_1 (A B : Type) (f : A -> B) :
  IsProper (_=_ ==> _=_) f.
Proof. intros x y a. induction a. apply id%type. Defined.

#[export] Instance is_proper_eq_2 (A0 A1 B : Type) (k : A0 -> A1 -> B) :
  IsProper (_=_ ==> _=_ ==> _=_) k.
Proof.
  intros x0 y0 a0 x1 y1 a1. induction a0. induction a1. apply id%type.
Defined.

(** ** Properties of the Identity Function *)

Section Context.

Context (A : Type).

#[export] Instance is_retr_eq_id :
  IsRetr (A := A) _=_ id id.
Proof. intros x. apply id%type. Defined.

#[export] Instance is_sect_eq_id :
  IsSect (A := A) _=_ id id.
Proof. intros x. apply id%type. Defined.

#[export] Instance is_iso_l_eq_id :
  IsIsoL (A := A) (B := A) _=_ _=_ id id.
Proof.
  split.
  - apply is_proper_eq_1.
  - apply is_proper_eq_1.
  - apply is_retr_eq_id.
Defined.

#[export] Instance is_iso_r_eq_id :
  IsIsoR (A := A) (B := A) _=_ _=_ id id.
Proof.
  split.
  - apply is_proper_eq_1.
  - apply is_proper_eq_1.
  - apply is_sect_eq_id.
Defined.

#[export] Instance is_bi_inv_eq_id :
  IsBiInv (A := A) (B := A) _=_ _=_ id.
Proof.
  split.
  - exists id. apply is_iso_l_eq_id.
  - exists id. apply is_iso_r_eq_id.
Defined.

#[export] Instance is_equiv_types_eq : A ~= A.
Proof. exists id. apply is_bi_inv_eq_id. Defined.

End Context.

(** ** Properties of Transport *)

Section Context.

Context (A B : Type) (e : A = B).

#[export] Instance is_retr_eq_transport_id :
  IsRetr _=_ (transport id e) (transport id (e ^-1)).
Proof. intros x. destruct e. apply id%type. Defined.

#[export] Instance is_sect_eq_transport_id :
  IsSect _=_ (transport id e) (transport id (e ^-1)).
Proof. intros x. destruct e. apply id%type. Defined.

#[export] Instance is_iso_l_eq_transport_id :
  IsIsoL _=_ _=_ (transport id e) (transport id (e ^-1)).
Proof.
  split.
  - apply is_proper_eq_1.
  - apply is_proper_eq_1.
  - apply is_retr_eq_transport_id.
Defined.

#[export] Instance is_iso_r_eq_transport_id :
  IsIsoR _=_ _=_ (transport id e) (transport id (e ^-1)).
Proof.
  split.
  - apply is_proper_eq_1.
  - apply is_proper_eq_1.
  - apply is_sect_eq_transport_id.
Defined.

#[export] Instance is_bi_inv_eq_transport_id :
  IsBiInv _=_ _=_ (transport id e).
Proof.
  split.
  - exists (transport id (e ^-1)). apply is_iso_l_eq_transport_id.
  - exists (transport id (e ^-1)). apply is_iso_r_eq_transport_id.
Defined.

#[export] Instance idtoeqv : A ~= B.
Proof. exists (transport id e). apply is_bi_inv_eq_transport_id. Defined.

End Context.

#[export] Instance is_refl_equiv_types_eq : IsRefl _~=_.
Proof. intros A. apply is_equiv_types_eq. Defined.

#[export] Instance is_sym_equiv_types_eq : IsSym _~=_.
Proof.
  intros A B [f [[g IIL] [h IIR]]].
  exists (g o f o h). split.
  - exists f. split.
    + apply is_proper_eq_1.
    + apply is_proper_eq_1.
    + intros y. unfold compose.
      pose proof retr (f := f) (g := g) (h y) as r.
      pose proof sect (f := f) (g := h) y as s.
      pose proof is_proper_eq_1 f r as p.
      apply (s o p)%type.
  - exists f. split.
    + apply is_proper_eq_1.
    + apply is_proper_eq_1.
    + intros x. unfold compose.
      pose proof sect (f := f) (g := h) (f x) as s.
      pose proof is_proper_eq_1 g s as p.
      pose proof retr (f := f) (g := g) x as r.
      apply (r o p)%type.
Defined.

#[export] Instance is_trans_equiv_types_eq : IsTrans _~=_.
Proof.
  intros A B C [f [[g IILf] [h IIRf]]] [i [[j IILi] [k IIRi]]].
  exists (i o f). split.
  - exists (g o j). split.
    + apply is_proper_eq_1.
    + apply is_proper_eq_1.
    + intros y. unfold compose.
      pose proof retr (f := i) (g := j) (f y) as ri.
      pose proof is_proper_eq_1 g ri as pi.
      pose proof retr (f := f) (g := g) y as rf.
      apply (rf o pi)%type.
  - exists (h o k). split.
    + apply is_proper_eq_1.
    + apply is_proper_eq_1.
    + intros y. unfold compose.
      pose proof sect (f := f) (g := h) (k y) as sf.
      pose proof is_proper_eq_1 i sf as pf.
      pose proof sect (f := i) (g := k) y as si.
      apply (si o pf)%type.
Defined.

(** One of these ways is probably better. *)

Definition is_equiv_transport (A : Type) (P : A -> Type)
  (x y : A) (e : x = y) : P x ~= P y.
Proof. destruct e. apply idtoeqv. apply id%type. Defined.

Definition is_equiv_transport' (A : Type) (P : A -> Type)
  (x y : A) (e : x = y) : P x ~= P y.
Proof.
  exists (transport P e). split.
  - exists (transport P (e ^-1)). split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros a. apply rew_opp_l.
  - exists (transport P (e ^-1)). split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros a. apply rew_opp_r.
Defined.

(** ** Proposition Extensionality *)

Class IsPropExt : Prop :=
  prop_ext (A B : Prop) (a : A <-> B) : A = B.

(** This lemma gets its name from [ZifyClasses.eq_iff]. *)

Lemma eq_iff (A B : Prop) (a : A = B) : A <-> B.
Proof. induction a. reflexivity. Qed.

(** ** Proposition Extensionality for Types *)

Class IsPropExtType : Prop :=
  prop_ext_type (A B : Type) `{!IsProp A} `{!IsProp B}
  (a : (A -> B) * (B -> A)) : A = B.

Lemma eq_iff_type (A B : Type) `{!IsProp A} `{!IsProp B}
  (a : A = B) : (A -> B) * (B -> A).
Proof. induction a. split; apply id. Defined.

(** ** Predicate Extensionality *)

Class IsPredExt : Prop :=
  pred_ext (A : Type) (P Q : A -> Prop) (a : forall x : A, P x <-> Q x) : P = Q.

(** ** Predicate Extensionality Axiom *)

Axiom predicate_extensionality :
  forall (A : Type) (P Q : A -> Prop) (a : forall x : A, P x <-> Q x),
  P = Q.

(** ** Function Extensionality *)

Class IsFunExt : Prop :=
  fun_ext (A B : Type) (f g : A -> B) (a : forall x : A, f x = g x) : f = g.

(** This lemma gets its name from [FunctionalExtensionality.equal_f]. *)

Lemma equal_f (A B : Type) (f g : A -> B) (a : f = g) (x : A) : f x = g x.
Proof. induction a. reflexivity. Qed.

(** ** Dependent Function Extensionality *)

Class IsFunExtDep : Prop :=
  fun_ext_dep (A : Type) (P : A -> Type)
  (f g : forall x : A, P x) (a : forall x : A, f x = g x) : f = g.

(** Dependent function extensionality implies function extensionality. *)

#[export] Instance fun_ext_dep_is_fun_ext
  `{!IsFunExtDep} : IsFunExt.
Proof. intros A B f g a. apply fun_ext_dep. intros x. apply a. Qed.

(** ** Type Extensionality *)

Class IsTypeExt : Prop :=
  type_ext (A B : Type) (f : A -> B) (g : B -> A)
  (r : forall x : A, g (f x) = x) (s : forall y : B, f (g y) = y) :
  A = B.

(** ** Type Extensionality Axiom *)

Axiom type_extensionality : forall (A B : Type)
 (f : A -> B) (g : B -> A)
 (r : forall x : A, g (f x) = x) (s : forall y : B, f (g y) = y),
 A = B.

(** ** Univalence *)

Class IsUniv : Prop :=
  uam (A B : Type) `{!A ~= B} : A = B.

(** ** Univalence Axiom *)

Axiom univalence : forall A B : Type,
  IsBiInv _=_ _=_ (idtoeqv (A := A) (B := B)).

(** This is axiom 2.10.3 and its corollaries from the book. *)

Corollary ua_equiv (A B : Type) : (A = B) ~= (A ~= B).
Proof. exists idtoeqv. apply univalence. Defined.

Lemma ua (A B : Type) `{!A ~= B} : A = B.
Proof.
  pose proof equiv_types_bi_inv A B _=_ _=_ as IET.
  pose proof univalence A B as IBI.
  pose proof l_inv_iso_l as ILI.
  pose proof ex_proj1 ILI as e.
  apply e. apply IET.
Defined.

Arguments ua {_ _} _.

(** Propositional extensionality
    makes functional extensionality an equality. *)

Lemma prop_fun_ext_dep `{IsPropExt} `{IsFunExtDep}
  (A : Type) (P : A -> Type) (f g : forall x : A, P x) :
  (forall x : A, f x = g x) = (f = g).
Proof.
  apply prop_ext. split.
  - intros a. apply fun_ext_dep. intros x. apply a.
  - intros a x. apply equal_f_dep. apply a.
Qed.

(** Families of propositions are propositions. *)

Lemma eq_pi_is_prop `{IsFunExtDep} (A : Type) (P : A -> Prop)
  `{!forall x : A, IsProp (P x)} : IsProp (forall x : A, P x).
Proof.
  match goal with
  | h : forall _ : _, IsProp _ |- _ => rename h into p
  end.
  intros g h. apply fun_ext_dep. intros x. apply p.
Qed.

(** Families of contractible types are contractible. *)

Lemma eq_pi_is_contr `{IsFunExtDep} (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} : IsContr (forall x : A, P x).
Proof.
  match goal with
  | h : forall _ : _, IsContr _ |- _ => rename h into c
  end.
  apply @inhabited_prop_is_contr.
  - intros x. apply c.
  - apply (@eq_pi_is_prop _). intros x. apply contr_is_prop.
Qed.

Module HomotopyTypicalDigression.

#[local] Open Scope ex_scope.
#[local] Open Scope sig_scope.

(** This is lemma 3.11.7 from the book. *)

Lemma ret (A B : Type) `{!IsRetrType A B _=_}
  `{!IsContr A} : IsContr B.
Proof.
  destruct IsRetrType0 as [f [g IR]]. destruct contr as [x h].
  exists (f x). intros y. rewrite <- (sect (f := f) y). f_equal. apply h.
Qed.

(** This is lemma 3.11.8 from the book. *)

Lemma sig_contr (A : Type) (a : A) : IsContr {x : A | a = x}.
Proof.
  exists (a; id%type). intros [x e]. destruct e. apply id%type.
Defined.

(** This was definition 4.2.4 from the book. *)

Definition cf (A : Type) (P : A -> Prop) (x : A)
  (s : {a : {x : A | P x} | x = proj1_sig a}) : P x.
Proof. destruct s as [[y a] e]. simpl in e. induction e. apply a. Defined.

Definition cg (A : Type) (P : A -> Prop) (x : A)
  (a : P x) : {a : {x : A | P x} | x = proj1_sig a}.
Proof. exists (x; a). reflexivity. Defined.

Lemma classes (A : Type) (P : A -> Prop) (x : A) :
  IsIso _=_ _=_ cf (cg P x).
Proof.
  split.
  - split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros [[y a] e]. simpl in e. unfold cf, cg. rewrite e. reflexivity.
  - split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros a. unfold cf, cg. reflexivity.
Qed.

(** This is lemma 4.8.1 from the book. *)

Lemma classifier (A : Type) (P : A -> Prop) (x : A) :
  IsEquivTypes (fib _=_ (proj1_sig (P := P)) x) (P x) _=_ _=_.
Proof. exists cf. split; exists (cg P x); apply classes. Qed.

Lemma ua_elim (A B : Type) (e : A = B) :
  idtoeqv e = (transport id e; is_bi_inv_eq_transport_id e)%ex.
Proof. reflexivity. Defined.

Lemma ua_comp (A B : Type) (e : A ~= B) :
  idtoeqv (ua e) = e.
Proof.
  unfold ua.
  unfold equiv_types_bi_inv, l_inv_iso_l.
  unfold bi_inv_is_l_inv.
  destruct (univalence A B) as [[f IIL] [g IIR]].
  unfold ex_proj1.
  pose proof retr (f := idtoeqv) (g := f) (g e) as r.
  pose proof sect (f := idtoeqv) (g := g) e as s.
  pose proof is_proper_eq_1 f s as p.
  pose proof (r o p ^-1)%type as c.
  pose proof is_proper_eq_1 idtoeqv c as q.
  apply (s o q)%type.
Defined.

Lemma ua_uniq (A B : Type) (e : A = B) :
  ua (idtoeqv e) = e.
Proof.
  unfold ua.
  unfold equiv_types_bi_inv, l_inv_iso_l.
  unfold bi_inv_is_l_inv.
  destruct (univalence A B) as [[f IIL] [g IIR]].
  unfold ex_proj1.
  pose proof retr (f := idtoeqv) (g := f) e as r.
  apply r.
Defined.

Lemma ua_refl (A : Type) :
  ua (refl (Reflexive := is_refl_equiv_types_eq) A) =
  @eq_refl Type A.
Proof.
  unfold ua.
  unfold equiv_types_bi_inv, l_inv_iso_l.
  unfold bi_inv_is_l_inv.
  destruct (univalence A A) as [[f IIL] [g IIR]].
  unfold ex_proj1.
  pose proof retr (f := idtoeqv) (g := f) id%type as r.
  apply r.
Defined.

(** These would probably go with some effort. *)

Lemma ua_sym (A B : Type) (e : A ~= B) :
  ua (sym (Symmetric := @is_sym_equiv_types_eq) A B e) =
  @eq_sym Type A B (ua e).
Proof.
  unfold ua.
  unfold equiv_types_bi_inv, l_inv_iso_l.
  unfold bi_inv_is_l_inv.
  destruct (univalence A B) as [[fAB IILAB] [gAB IIRAB]],
  (univalence B A) as [[fBA IILBA] [gBA IIRBA]].
  unfold ex_proj1.
  pose proof retr (f := idtoeqv) (g := fBA) as r.
  pose proof sect (f := idtoeqv) (g := gAB) as s'.
  pose proof sect (f := idtoeqv) (g := gBA) as s.
  pose proof retr (f := idtoeqv) (g := fAB) as r'.
  rewrite <- r.
  f_equal.
  rewrite <- s at 1.
  f_equal.
Admitted.

(*
Lemma eq_trans (A : Type) (x y z : A) (e : x = y) (f : y = z) : x = z.
Proof. induction e using eq_rect. induction f using eq_rect. apply eq_refl. Defined.
*)

Lemma ua_trans (A B C : Type) (e : A ~= B) (f : B ~= C) :
  ua (trans (Transitive := @is_trans_equiv_types_eq) A B C e f) =
  @eq_trans Type A B C (ua e) (ua f).
Proof.
  rewrite <- (ua_comp e) at 1.
  rewrite <- (ua_comp f) at 1.
  replace (@RelationClasses.transitivity Type
        (fun A B : Type => IsEquivTypes A B (@eq A) (@eq B))
        (@is_trans_equiv_types_eq) A B C (@idtoeqv A B (@ua A B e))
        (@idtoeqv B C (@ua B C f)))
  with (idtoeqv (ua f o ua e)%type).
  2:{ pose proof transport_trans id (ua e) (ua f) as t.
    pose proof functional_extensionality _ _ t as t'; cbv beta in t'.
    unfold idtoeqv.
    admit. } rewrite ua_uniq. reflexivity.
Restart.
  unfold ua.
  unfold equiv_types_bi_inv, l_inv_iso_l.
  unfold bi_inv_is_l_inv.
  destruct (univalence A B) as [[fAB IILAB] [gAB IIRAB]],
  (univalence B C) as [[fBC IILBC] [gBC IIRBC]],
  (univalence A C) as [[fAC IILAC] [gAC IIRAC]].
  unfold ex_proj1.
Admitted.

(** This is lemma 4.9.2 from the book. *)

Lemma easy (A B X : Type) (e : A ~= B) : (X -> A) ~= (X -> B).
Proof.
  destruct (ua e).
  apply idtoeqv.
  reflexivity.
Defined.

Definition inj1_sig (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} (x : A) : {x : A | P x} :=
  (x; ex_proj1 contr).

Lemma what (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} : IsRetr _=_ proj1_sig inj1_sig.
Proof.
  intros [x a]. unfold proj1_sig, inj1_sig. f_equal.
  pose proof ex_proj2 contr a as b. apply b.
Qed.

Lemma what' (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} : IsSect _=_ proj1_sig inj1_sig.
Proof. intros x. unfold proj1_sig, inj1_sig. reflexivity. Qed.

(** This is part of corollary 4.9.3 from the book. *)

Lemma alpha (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} (f : A -> {x : A | P x}) (x : A) : A.
Proof. apply (proj1_sig (f x)). Defined.

(** This is corollary 4.9.3 from the book. *)

Lemma before_why (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} :
  IsBiInv _=_ _=_ (proj1_sig (P := P)).
Proof. split; exists inj1_sig; split;
  try typeclasses eauto; apply what || apply what'.
Qed.

Lemma why (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} :
  {x : A | P x} ~= A.
Proof. exists proj1_sig. apply before_why. Qed.

Lemma why_squared (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} :
  (A -> {x : A | P x}) ~= (A -> A).
Proof. apply easy. apply why. Qed.

(** These are parts of theorem 4.9.4 from the book. *)

Lemma phi (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} :
  (forall x : A, P x) -> (fib _=_ alpha id%core).
Proof. intros f. hnf. exists (fun x : A => (x; f x)). apply id%type. Defined.

Lemma psi (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} :
  (fib _=_ alpha id%core) -> (forall x : A, P x).
Proof.
  intros gp x.
  apply (transport P (happly (proj2_sig gp ^-1) x)
  (proj2_sig (proj1_sig gp x))).
Defined.

Lemma eq_pi_is_what (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} :
  IsRetrType (fib _=_ alpha id%core) (forall x : A, P x) _=_.
Proof.
  match goal with
  | x : forall _ : _, IsContr _ |- _ => rename x into c
  end.
  exists psi, phi. intros f. unfold phi. unfold psi. cbn. reflexivity.
Defined.

Lemma rew_id_l (A : Type) (x y : A) (e : x = y) :
  (e o id = e)%type.
Proof. destruct e. apply id%type. Defined.

Lemma rew_id_r (A : Type) (x y : A) (e : x = y) :
  (id o e = e)%type.
Proof. destruct e. apply id%type. Defined.

Theorem go_there (A B : Type) (f : A -> B) (y : B) (s t : fib _=_ f y) :
  (s = t) -> {g : proj1_sig s = proj1_sig t |
  proj2_sig t o f_equal f g = proj2_sig s}%type.
Proof.
  intros e. destruct s as [x p], t as [x' p']. cbn. cbv in e.
  inversion_sigma e as [e' e'']. destruct e'. cbv in e''. subst p'.
  exists id%type. unfold f_equal. apply rew_id_l.
Defined.

Theorem come_here (A B : Type) (f : A -> B) (y : B) (s t : fib _=_ f y) :
  {g : proj1_sig s = proj1_sig t |
  proj2_sig t o f_equal f g = proj2_sig s}%type -> (s = t).
Proof.
  intros [e e']. destruct s as [x p], t as [x' p']. cbn in *.
  subst x'. f_equal. subst p. unfold f_equal. apply rew_id_l.
Defined.

(** This is lemma 4.2.5 from the book. *)

Theorem fine (A B : Type) (f : A -> B) (y : B) (s t : fib _=_ f y) :
  (s = t) ~= {g : proj1_sig s = proj1_sig t |
  proj2_sig t o f_equal f g = proj2_sig s}%type.
Proof.
  exists (go_there (s := s) (t := t)). split.
  - exists (come_here s t). repeat (split; try typeclasses eauto).
    intros e.
    destruct s as [x p], t as [x' p'].
    unfold go_there, come_here. admit.
  - exists (come_here s t). repeat (split; try typeclasses eauto).
    intros [e e'].
    destruct s as [x p], t as [x' p']. cbn in e, e'.
    unfold go_there, come_here. admit.
Admitted.

(** This is theorem 4.2.6 from the book. *)

Theorem curses (A B : Type) (f : A -> B) (y : B)
  `{!IsHAE _=_ _=_ f} : IsContr (fib _=_ f y).
Proof.
  match goal with
  | x : IsHAE _ _ _ |- _ => rename x into IHAE
  end.
  destruct IHAE as [g [[[] []] c]].
  hnf. unfold fib.
  set (x := g y).
  set (e := sect (f := f) (g := g) _ : f x = y).
  exists (x; e). intros [x' e']. apply come_here.
  pose proof retr (f := f) as r.
  pose proof sect (f := f) as s.
  pose proof (e' ^-1 o e)%type as t.
  pose proof is_proper_eq_1 g t as p.
  do 2 rewrite r in p. exists p. cbn. destruct p. unfold f_equal.
  unfold Isomorphic.iso_l_is_proper_f in c.
  subst e. cbn. pose proof c (g y) as c'.
Admitted.

(** This is an approximation of theorem 4.2.6 from the book. *)

Theorem curses' (A B : Type) (f : A -> B) (y : B)
  `{!IsSet B}
  `{!IsBiInv _=_ _=_ f} : IsContr (fib _=_ f y).
Proof.
  match goal with
  | x : IsBiInv _ _ _ |- _ => rename x into IBI
  end.
  destruct IBI as [[g IIL] [h IIR]].
  hnf. unfold fib.
  set (x := g y).
  assert (e : f x = y).
  { pose proof retr (f := f) as r.
    pose proof sect (f := f) as s.
    subst x.
    rewrite <- s. f_equal. rewrite <- r. f_equal. rewrite s.
    reflexivity. }
  exists (x; e). intros [x' e']. subst x.
  pose proof retr (f := f) as r.
  pose proof sect (f := f) as s.
  pose proof (e' ^-1 o e)%type as t.
  pose proof is_proper_eq_1 g t as p.
  do 2 rewrite r in p. subst x'. f_equal. apply uip.
Defined.

(** This is theorem 4.9.4 from the book. *)

Lemma eq_pi_is_contr' (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} : IsContr (forall x : A, P x).
Proof.
  match goal with
  | h : forall _ : _, IsContr _ |- _ => rename h into c
  end.
  pose proof eq_pi_is_what as w.
  pose proof @ret (fib _=_ alpha id%core) (forall x : A, P x) w as r.
  apply r.
  apply curses.
  (** This requires more lemmas. *)
Admitted.

(** This is theorem 4.9.5 from the book. *)

Lemma conclusion (A : Type) (P : A -> Type) (f g : forall x : A, P x) :
  IsBiInv _=_ _=_ (happly (f := f) (g := g)).
Proof.
  epose proof (need_this _) as one.
  (** This requires more effort. *)
Admitted.

Lemma fun_now : IsFunExt.
Proof.
  intros A B f g e.
  epose proof (conclusion f g) as two.
  destruct two as [[h IIL] IRI]. auto.
Qed.

(** This should follow. *)

Lemma more_fun_now : IsFunExtDep.
Proof.
  intros A P f g e.
  epose proof (conclusion f g) as two.
  destruct two as [[h IIL] IRI]. auto.
Qed.

End HomotopyTypicalDigression.

(** Families of sets are sets. *)

Lemma eq_pi_is_set `{IsPropExt} `{IsFunExtDep} (A : Type) (P : A -> Prop)
  `{!forall x : A, IsSet (P x)} : IsSet (forall x : A, P x).
Proof.
  match goal with
  | h : forall _ : _, IsSet _ |- _ => rename h into s
  end.
  intros f g.
  pose proof prop_fun_ext_dep f g as t. rewrite <- t. clear t.
  apply (@eq_pi_is_prop _).
  intros x. apply @set_is_prop_eq. apply s.
Qed.

(** Fibrations are at the same homotopy level as their fibers. *)

Lemma eq_h_level_is_h_level `{IsPropExt} `{IsFunExtDep}
  (A : Type) (P : A -> Prop) (n : nat)
  `{!forall x : A, IsHLevel n (P x)} : IsHLevel n (forall x : A, P x).
Proof.
  match goal with
  | h : forall _ : _, IsHLevel _ _ |- _ => rename h into a
  end.
  revert A P a. induction n as [| p b]; intros A P a.
  - apply @contr_is_h_level_0. apply (@eq_pi_is_contr _).
    intros x. apply @h_level_0_is_contr. apply a.
  - intros f g.
    pose proof prop_fun_ext_dep f g as t. rewrite <- t. clear t.
    apply b. intros x. apply h_level_S_is_h_level_eq. apply a.
Qed.

(** Univalence implies type extensionality. *)

#[export] Instance univ_is_type_ext `{IsUniv} : IsTypeExt.
Proof.
  intros A B f g r s. apply ua. exists f. split.
  - exists g. split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros x. apply r.
  - exists g. split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros y. apply s.
Qed.

Module FromAxioms.

#[export] Instance is_prop_ext : IsPropExt.
Proof. intros A B. apply propositional_extensionality. Qed.

#[export] Instance is_prop_ext_type : IsPropExtType.
Proof.
  intros A B IPA IPB [f g]. pose proof univalence A B as s.
  destruct s as [ua [IPidtoeqv IPua]]. apply ua. exists f. split.
  - exists g. split; try typeclasses eauto. intros x. apply irrel.
  - exists g. split; try typeclasses eauto. intros x. apply irrel.
Qed.

#[export] Instance is_pred_ext : IsPredExt.
Proof. intros A P Q. apply predicate_extensionality. Qed.

#[export] Instance is_fun_ext : IsFunExt.
Proof. intros A B. apply functional_extensionality. Qed.

#[export] Instance is_fun_ext_dep : IsFunExtDep.
Proof. intros A P. apply functional_extensionality_dep. Qed.

#[export] Instance is_type_ext : IsTypeExt.
Proof. intros A B. apply type_extensionality. Qed.

#[export] Instance is_univ : IsUniv.
Proof. intros A B. apply univalence. Qed.

End FromAxioms.
