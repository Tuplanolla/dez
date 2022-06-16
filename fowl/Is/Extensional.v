(** * Extensionality and Univalence *)

From Coq Require Import
  Logic.FunctionalExtensionality Logic.ProofIrrelevance
  Logic.PropExtensionality Logic.PropExtensionalityFacts.
From DEZ.Is Require Export
  Irrelevant Isomorphic.

(** We declare various axiom schemes as classes
    in hopes of one day turning them into theorems. *)

Theorem ac (A B : Type) (R : A -> B -> Prop)
  (g : forall x : A, {y : B | R x y}) :
  {f : A -> B | forall x : A, R x (f x)}.
Proof.
  exists (fun x : A => proj1_sig (g x)).
  intros x. set (p := g x). induction p as [y p]. cbn. apply p.
Defined.

Theorem dpb (A B : Type) (R : A -> B -> Prop)
  (s : {f : A -> B | forall x : A, R x (f x)}) (x : A) :
  {y : B | R x y}.
Proof.
  induction s as [f g]. exists (f x). apply (g x).
Defined.

(** This is lemma 2.15.6 from the book. *)

Theorem ac_eq (A : Type) (P : A -> Type) (R : forall x : A, P x -> Prop)
  (f : forall x : A, {a : P x | R x a}) :
  {g : forall x : A, P x | forall x : A, R x (g x)}.
Proof.
  exists (fun x : A => proj1_sig (f x)). intros x. set (f x) as y.
  destruct y as [a s]. apply s.
Defined.

Theorem ac_eq_ex (A : Type) (P : A -> Prop) (R : forall x : A, P x -> Prop)
  (f : forall x : A, exists a : P x, R x a) :
  exists g : forall x : A, P x, forall x : A, R x (g x).
Proof.
  exists (fun x : A => ex_proj1 (f x)). intros x. set (f x) as y.
  destruct y as [a s]. apply s.
Defined.

(** This is part of theorem 2.15.7 from the book. *)

Theorem dbp_eq (A : Type) (P : A -> Type) (R : forall x : A, P x -> Prop)
  (s : {g : forall x : A, P x | forall x : A, R x (g x)}) (x : A) :
  {a : P x | R x a}.
Proof.
  destruct s as [g f]. exists (g x). apply (f x).
Defined.

Theorem dbp_eq_ex (A : Type) (P : A -> Prop) (R : forall x : A, P x -> Prop)
  (s : exists g : forall x : A, P x, forall x : A, R x (g x)) (x : A) :
  exists a : P x, R x a.
Proof.
  destruct s as [g f]. exists (g x). apply (f x).
Defined.

(** TODO Clean up this mess. *)

Reserved Notation "x '_*'" (left associativity, at level 20).
Reserved Notation "x '~=' y" (no associativity, at level 70).

(** This is lemma 2.3.1 from the book. *)

Definition transport (A : Type) (P : A -> Type)
  (x y : A) (e : x = y) (a : P x) : P y.
Proof.
  induction e. apply a.
Defined.

Definition transport_dep
  (A : Type) (P : A -> Type) (Q : forall x : A, P x -> Type)
  {x y : A} (e : x = y) (p : P x) (q : Q x p) :
  Q y (transport P e p).
Proof.
  destruct e. apply q.
Defined.

#[local] Notation "'_*_'" := (transport _) (only parsing).
#[local] Notation "e '_*'" := (transport _ e) (only parsing).

(** This is lemma 2.2.1 from the book. *)

Lemma ap (A B : Type) (f : A -> B) (x y : A) (e : x = y) : f x = f y.
Proof.
  apply (transport (fun y : A => f x = f y) e). apply id%type.
Defined.

(** This is lemma 2.3.4 from the book. *)

Lemma apd (A : Type) (P : A -> Type)
  (f : forall x : A, P x) (x y : A) (e : x = y) :
  e _* (f x) = f y.
Proof.
  destruct e. apply id%type.
Defined.

Section Context.

Context (A B C : Type)
  (f : A -> B) (g : B -> C) (x y z : A) (e : x = y) (d : y = z).

#[local] Open Scope type_scope.

(** This is lemma 2.2.1 from the book. *)

Lemma ap_refl : ap (y := x) f id = id.
Proof. clear. apply id%type. Defined.

(** This is lemma 2.2.2 from the book. *)

Lemma ap_id : ap id%core e = e.
Proof. clear. destruct e. apply id%type. Defined.

Lemma ap_ap : ap g (ap f e) = ap (g o f)%core e.
Proof. clear. destruct e. apply id%type. Defined.

Lemma ap_sym : ap f (e ^-1) = ap f e ^-1.
Proof. clear. destruct e. apply id%type. Defined.

Lemma ap_trans : ap f (d o e) = ap f d o ap f e.
Proof. clear. destruct d. destruct e. apply id%type. Defined.

End Context.

Lemma happly_nondep (A B : Type) (f g : A -> B) (e : f = g) (x : A) : f x = g x.
Proof.
  apply (transport (fun h : A -> B => f x = h x) e). apply id%type.
Defined.

Lemma happly (A : Type) (P : A -> Type)
  (f g : forall x : A, P x) (e : f = g) (x : A) : f x = g x.
Proof.
  apply (transport (fun h : forall x : A, P x => f x = h x) e). apply id%type.
Defined.

Arguments happly {_ _} _ _ _ _.

Class IsEquivTypesEq (A B : Type) : Type :=
  equiv_types_eq_equiv_types :> IsEquivTypes A B _=_ _=_.

#[local] Notation "'_~=_'" := IsEquivTypesEq.
#[local] Notation "A '~=' B" := (IsEquivTypesEq A B).

Definition transport_refl (A : Type) (P : A -> Type) (x : A) (a : P x) :
  transport P id%type a = a.
Proof. apply id%type. Defined.

(** This is lemma 2.3.9 from the book. *)

Definition transport_trans (A : Type) (P : A -> Type)
  (x y z : A) (e : x = y) (f : y = z) (a : P x) :
  (* f _* (e _* a) = (f o e)%type _* a *)
  transport P f (transport P e a) = transport P (f o e)%type a.
Proof.
  destruct e, f. apply id%type.
Defined.

(** This is lemma 2.3.10 from the book. *)

Definition transport_ap (A B : Type) (P : B -> Type)
  (f : A -> B) (x y : A) (e : x = y) (a : P (f x)) :
  transport P (ap f e) a = transport (P o f) e a.
Proof.
  destruct e. apply id%type.
Defined.

(** This is lemma 2.3.11 from the book. *)

Definition transport_f (A : Type) (P Q : A -> Type)
  (f : forall x : A, P x -> Q x) (x y : A) (e : x = y) (a : P x) :
  transport Q e (f x a) = f y (transport P e a).
Proof.
  destruct e. apply id%type.
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

Theorem do_not_need_this_ex (A : Type) (P : A -> Prop) (R : forall x : A, P x -> Prop) :
  IsLInv _=_ _=_ (@ac_eq_ex A P R).
Proof.
  exists (@dbp_eq_ex A P R). split.
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

Theorem need_this_ex (A : Type) (P : A -> Prop) (R : forall x : A, P x -> Prop) :
  IsRInv _=_ _=_ (@ac_eq_ex A P R).
Proof.
  exists (@dbp_eq_ex A P R). split.
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

Theorem this_is_equiv_ex (A : Type) (P : A -> Prop) (R : forall x : A, P x -> Prop) :
  IsBiInv _=_ _=_ (@ac_eq_ex A P R).
Proof.
  split.
  - apply do_not_need_this_ex.
  - apply need_this_ex.
Defined.

Theorem seriously (A : Type) (P : A -> Type) (R : forall x : A, P x -> Prop) :
  (forall x : A, {a : P x | R x a}) ~=
  {g : forall x : A, P x | forall x : A, R x (g x)}.
Proof. exists ac_eq. apply this_is_equiv. Defined.

Theorem seriously_ex (A : Type) (P : A -> Prop) (R : forall x : A, P x -> Prop) :
  (forall x : A, exists a : P x, R x a) ~=
  exists g : forall x : A, P x, forall x : A, R x (g x).
Proof. exists ac_eq_ex. apply this_is_equiv_ex. Defined.

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

#[export] Instance refl :
  forall A : Type, A ~= A.
Proof. intros A. apply is_equiv_types_eq. Defined.

#[export] Instance sym :
  forall A B : Type, A ~= B -> B ~= A.
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

#[export] Instance trans :
  forall A B C : Type, A ~= B -> B ~= C -> A ~= C.
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

Arguments refl _ : clear implicits.
Arguments sym _ _ _ : clear implicits.
Arguments trans _ _ _ _ _ : clear implicits.

Lemma idtoeqv_refl (A : Type) :
  idtoeqv id%type = refl A.
Proof. reflexivity. Defined.

Lemma idtoeqv_sym (A B : Type) (e : A = B) :
  idtoeqv (e ^-1) = sym A B (idtoeqv e).
Proof. destruct e. reflexivity. Defined.

Lemma idtoeqv_trans (A B C : Type) (e : A = B) (f : B = C) :
  idtoeqv (f o e)%type = trans A B C (idtoeqv e) (idtoeqv f).
Proof. destruct e. destruct f. reflexivity. Defined.

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
    + intros a.
      pose proof transport_trans P e (e ^-1) a as f.
      pose proof eq_trans_sym_inv_r e as g.
      apply (transport (fun b : P _ => b = a) (f ^-1)).
      apply (transport (fun b : _ = _ => transport P b a = a) (g ^-1)).
      apply transport_refl.
  - exists (transport P (e ^-1)). split.
    + typeclasses eauto.
    + typeclasses eauto.
    + intros a.
      pose proof transport_trans P (e ^-1) e a as f.
      pose proof eq_trans_sym_inv_l e as g.
      apply (transport (fun b : P _ => b = a) (f ^-1)).
      apply (transport (fun b : _ = _ => transport P b a = a) (g ^-1)).
      apply transport_refl.
Defined.

(** This is equation 2.6.1 from the book. *)

Lemma prod_go (A B : Type)
  (a b : A * B) (e : a = b) : (fst a = fst b) * (snd a = snd b).
Proof.
  destruct a as [x y], b as [x' y'].
  pose proof ap fst e as f. apply (_,_).
  - apply f.
  - pose proof ap snd e as g. apply g.
Defined.

(** This is equation 2.6.3 from the book. *)

Lemma prod_come (A B : Type)
  (a b : A * B) (c : (fst a = fst b) * (snd a = snd b)) : a = b.
Proof.
  destruct c as [f g].
  destruct a as [x y], b as [x' y'].
  pose proof transport (fun x' : A => (x, y) = (x', y')) f as a. apply a.
  pose proof transport (fun y' : B => (x, y) = (x, y')) g as b. apply b.
  apply id%type.
Defined.

(** This is theorem 2.6.2 from the book. *)

#[export] Instance prod_is_bi_inv (A B : Type) (a b : A * B) :
  IsBiInv _=_ _=_ (prod_go (a := a) (b := b)).
Proof.
  split.
  - exists (prod_come a b). split.
    + apply is_proper_eq_1.
    + apply is_proper_eq_1.
    + intros e. destruct e. destruct a as [x y]. reflexivity.
  - exists (prod_come a b). split.
    + apply is_proper_eq_1.
    + apply is_proper_eq_1.
    + destruct a as [x y], b as [x' y']. intros [e f]. cbv in e, f.
      destruct e. destruct f. reflexivity.
Defined.

#[export] Instance prod_is_equiv_types (A B : Type) (a b : A * B) :
  (a = b) ~= (fst a = fst b) * (snd a = snd b).
Proof. exists prod_go. typeclasses eauto. Defined.

Equations prod_family (A : Type) (P Q : A -> Type) (x : A) : Type :=
  prod_family P Q x := P x * Q x.

(** This is theorem 2.6.4 from the book. *)

Lemma transport_prod (A : Type) (P Q : A -> Type)
  (x y : A) (e : x = y) (a : P x * Q x) :
  transport (prod_family P Q) e a =
  (transport P e (fst a), transport Q e (snd a)).
Proof.
  destruct e. destruct a as [p q]. apply id%type.
Defined.

#[local] Open Scope sig_scope.

Lemma sig_go (A : Type) (P : A -> Prop)
  (a b : {x : A | P x}) (e : a = b) :
  {f : proj1_sig a = proj1_sig b | transport P f (proj2_sig a) = proj2_sig b}.
Proof.
  destruct a as [x p], b as [x' p'].
  pose (ap proj1_sig e) as f. cbn in *.
  pose proof apd (P := P o proj1_sig) proj2_sig e as g. cbn in *.
  exists f. rewrite <- transport_ap in g. apply g.
Defined.

Lemma sig_come (A : Type) (P : A -> Prop)
  (a b : {x : A | P x}) (c : {f : proj1_sig a = proj1_sig b |
  transport P f (proj2_sig a) = proj2_sig b}) : a = b.
Proof.
  destruct c as [f g].
  destruct a as [x p], b as [x' p'].
  cbn in *. destruct f. destruct g. apply id%type.
Defined.

(** This is theorem 2.7.2 from the book. *)

#[export] Instance sig_is_bi_inv (A : Type) (P : A -> Prop)
  (a b : {x : A | P x}) :
  IsBiInv _=_ _=_ (sig_go (a := a) (b := b)).
Proof.
  split.
  - exists (sig_come a b). split.
    + apply is_proper_eq_1.
    + apply is_proper_eq_1.
    + intros e. destruct e. destruct a as [x y]. reflexivity.
  - exists (sig_come a b). split.
    + apply is_proper_eq_1.
    + apply is_proper_eq_1.
    + destruct a as [x y], b as [x' y']. intros [e f]. cbv in e, f.
      destruct e. destruct f. reflexivity.
Defined.

#[export] Instance sig_is_equiv_types (A : Type) (P : A -> Prop)
  (a b : {x : A | P x}) :
  (a = b) ~= {f : proj1_sig a = proj1_sig b |
  transport P f (proj2_sig a) = proj2_sig b}.
Proof. exists sig_go. typeclasses eauto. Defined.

Equations sig_family (A : Type) (P : A -> Prop) (Q : {x : A | P x} -> Prop)
  (x : A) : Type :=
  sig_family Q x := {a : P x | Q (x; a)}.

Arguments sig_family {_} _ _ _.

(** This is theorem 2.7.4 from the book. *)

Lemma transport_sig (A : Type) (P : A -> Prop) (Q : {x : A | P x} -> Prop)
  (x y : A) (e : x = y) (a : {a : P x | Q (x; a)}) :
  transport (sig_family P Q) e a =
  (transport P e (proj1_sig a);
  transport_dep (sig_curry Q) e (proj1_sig a) (proj2_sig a)).
Proof.
  destruct e. destruct a as [p q]. apply id%type.
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

(** ** Proposition Extensionality Axiom for Types *)

Axiom propositional_extensionality_type :
  forall (A B : Type) (p : forall x y : A, x = y) (q : forall x y : B, x = y)
  (a : (A -> B) * (B -> A)), A = B.

Lemma eq_iff_type (A B : Type) `{!IsProp A} `{!IsProp B}
  (a : A = B) : (A -> B) * (B -> A).
Proof. induction a. split; apply id. Defined.

(** ** Predicate Extensionality *)

Class IsPredExt : Prop :=
  pred_ext (A : Type) (P Q : A -> Prop) (a : forall x : A, P x <-> Q x) : P = Q.

(** ** Predicate Extensionality Axiom *)

Axiom predicate_extensionality :
  forall (A : Type) (P Q : A -> Prop)
  (a : forall x : A, P x <-> Q x), P = Q.

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
  `{!IsRetr _=_ f g} `{!IsSect _=_ f g} : A = B.

(** ** Type Extensionality Axiom *)

Axiom type_extensionality : forall (A B : Type)
 (f : A -> B) (g : B -> A)
 (r : forall x : A, g (f x) = x) (s : forall y : B, f (g y) = y),
 A = B.

(** ** Univalence *)

Class IsUniv : Type :=
  univ_is_bi_inv (A B : Type) :> IsBiInv _=_ _=_ (idtoeqv (A := A) (B := B)).

(** ** Univalence Axiom *)

Axiom univalence : forall A B : Type,
  IsBiInv _=_ _=_ (idtoeqv (A := A) (B := B)).

(** This is axiom 2.10.3 and its corollaries from the book. *)

Corollary ua_equiv `{IsUniv} (A B : Type) : (A = B) ~= (A ~= B).
Proof. exists idtoeqv. typeclasses eauto. Defined.

(*
Lemma ua `{IsUniv} (A B : Type) `{!A ~= B} : A = B.
Proof.
  pose proof equiv_types_bi_inv A B _=_ _=_ as IET.
  pose proof univ_is_bi_inv A B as IBI.
  pose proof l_inv_iso_l as ILI.
  pose proof ex_proj1 ILI as e.
  apply e. apply IET.
Defined.
*)

Lemma ua (A B : Type) `{!A ~= B} : A = B.
Proof.
  pose proof equiv_types_bi_inv A B _=_ _=_ as IET.
  pose proof univalence A B as IBI.
  pose proof l_inv_iso_l as ILI.
  pose proof proj1_sig ILI as e.
  apply e. apply IET.
Defined.

Arguments ua {_ _} _.

Module HomotopyTypicalDigression.

#[local] Open Scope ex_scope.
#[local] Open Scope sig_scope.

(** This is lemma 3.11.7 from the book. *)

Lemma ret (A B : Type) `{!IsRetrType A B _=_}
  `{!IsContr A _=_} : IsContr B _=_.
Proof.
  destruct IsRetrType0 as [f [g IR]]. destruct contr as [x h].
  exists (f x). intros y. rewrite <- (sect (f := f) y). f_equal. apply h.
Qed.

(** This is lemma 3.11.8 from the book. *)

Lemma sig_contr (A : Type) (a : A) : IsContr {x : A | a = x} _=_.
Proof.
  exists (a; id%type). intros [x e]. destruct e. apply id%type.
Defined.

Lemma ex_contr (A : Type) (a : A) : IsContr (exists x : A, a = x) _=_.
Proof.
  exists (a; id%type)%ex. intros [x e]. destruct e. apply id%type.
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

Lemma classify (A : Type) (P : A -> Prop) (x : A) :
  IsBiInv _=_ _=_ (cf (P := P) (x := x)).
Proof. split; exists (cg P x); apply classes. Defined.

(** This is lemma 4.8.1 from the book. *)

Lemma classifier (A : Type) (P : A -> Prop) (x : A) :
  fib _=_ (proj1_sig (P := P)) x ~= P x.
Proof. exists cf. apply classify. Defined.

Lemma ua_elim (A B : Type) (e : A = B) :
  idtoeqv e = (transport id e; is_bi_inv_eq_transport_id e)%sigT.
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
  ua (refl A) = id%type.
Proof.
  rewrite <- ua_uniq. rewrite idtoeqv_refl. reflexivity.
Defined.

Lemma ua_sym (A B : Type) (e : A ~= B) :
  ua (sym A B e) = ua e ^-1.
Proof.
  rewrite <- ua_uniq. rewrite idtoeqv_sym. rewrite ua_comp. reflexivity.
Defined.

Lemma ua_trans (A B C : Type) (e : A ~= B) (f : B ~= C) :
  ua (trans A B C e f) = (ua f o ua e)%type.
Proof.
  rewrite <- ua_uniq. rewrite idtoeqv_trans. do 2 rewrite ua_comp. reflexivity.
Defined.

Lemma easy `{IsFunExtDep} (A B X : Type) (f : A -> B)
  (e : @IsBiInv A B _=_ _=_ f) : @IsBiInv (X -> A) (X -> B) _=_ _=_ (_o_ f).
Proof.
  destruct e as [[g ?] [h ?]].
  split.
  - exists (_o_ g). split; try typeclasses eauto.
    intros j. apply fun_ext_dep.
    intros x. unfold compose. rewrite retr. reflexivity.
  - exists (_o_ h). split; try typeclasses eauto.
    intros j. apply fun_ext_dep.
    intros x. unfold compose. rewrite sect. reflexivity.
Defined.

(** This is corollary 5.8.5 from the book. *)

Lemma equiv_ind (D : forall A B : Type, A ~= B -> Prop)
  (d : forall A : Type, D A A (refl A)) :
  forall (A B : Type) (e : A ~= B), D A B e.
Proof. intros A B e. rewrite <- (ua_comp e). destruct (ua e). apply d. Defined.

(** This is lemma 4.9.2 from the book. *)

Lemma also_easy (A B X : Type) (e : A ~= B) : (X -> A) ~= (X -> B).
Proof.
  destruct (ua e).
  apply refl.
Defined.

Definition inj1_sig (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x) _=_} (x : A) : {x : A | P x} :=
  (x; proj1_sig contr).

Lemma contr_is_retr_proj1_sig_inj1_sig (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x) _=_} : IsRetr _=_ proj1_sig inj1_sig.
Proof.
  intros [x a]. unfold proj1_sig, inj1_sig. f_equal.
  pose proof proj2_sig contr a as b. apply b.
Qed.

Lemma contr_is_sect_proj1_sig_inj1_sig (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x) _=_} : IsSect _=_ proj1_sig inj1_sig.
Proof. intros x. unfold proj1_sig, inj1_sig. reflexivity. Qed.

#[local] Instance dubious (A B C : Type) (f : A -> B)
  `{!IsBiInv _=_ _=_ f} : IsBiInv (A := C -> A) (B := C -> B) _=_ _=_ (_o_ f).
Proof.
  remember ((f; _ : IsBiInv _=_ _=_ f)%sigT : _ ~= _) as e eqn : h; cbn in h.
  rewrite <- (ua_comp e) in h.
  destruct (ua e).
  rewrite ua_elim in h.
  (** This projection requires [sig] instead of [ex]. *)
  apply (ap projT1) in h. cbn in h. subst f.
  split.
  - exists (_o_ id).
    split; try apply is_proper_eq_1.
    intros i. reflexivity.
  - exists (_o_ id).
    split; try apply is_proper_eq_1.
    intros i. reflexivity.
Defined.

(** This is part of corollary 4.9.3 from the book. *)

Lemma alpha (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x) _=_} (f : A -> {x : A | P x}) (x : A) : A.
Proof. apply (proj1_sig (f x)). Defined.

Lemma coalpha (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x) _=_} (f : A -> A) (x : A) : {x : A | P x}.
Proof. apply (inj1_sig (f x)). Defined.

(** This is corollary 4.9.3 from the book. *)

#[local] Instance before_why (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x) _=_} :
  IsBiInv _=_ _=_ (proj1_sig (P := P)).
Proof.
  split; exists inj1_sig; split;
  try typeclasses eauto;
  apply contr_is_retr_proj1_sig_inj1_sig ||
  apply contr_is_sect_proj1_sig_inj1_sig.
Defined.

Lemma why (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x) _=_} :
  {x : A | P x} ~= A.
Proof. exists proj1_sig. apply before_why. Defined.

Lemma why_squared (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x) _=_} :
  (A -> {x : A | P x}) ~= (A -> A).
Proof. apply also_easy. apply why. Defined.

Lemma after_why_squared (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x) _=_} :
  IsBiInv _=_ _=_ alpha.
Proof.
  match goal with
  | x : forall _ : _, IsContr _ _=_ |- _ => rename x into IC
  end.
  unfold alpha.
  pose proof dubious A (f := proj1_sig) as d.
  unfold compose in d.
  apply d.
Defined.

(** These are parts of theorem 4.9.4 from the book. *)

Lemma phi (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x) _=_} :
  (forall x : A, P x) -> (fib _=_ alpha id%core).
Proof. intros f. hnf. exists (fun x : A => (x; f x)). apply id%type. Defined.

Lemma psi (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x) _=_} :
  (fib _=_ alpha id%core) -> (forall x : A, P x).
Proof.
  intros gp x.
  apply (transport P (happly _ _ (proj2_sig gp ^-1) x)
  (proj2_sig (proj1_sig gp x))).
Defined.

Lemma eq_pi_is_what (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x) _=_} :
  IsRetrType (fib _=_ alpha id%core) (forall x : A, P x) _=_.
Proof.
  match goal with
  | x : forall _ : _, IsContr _ _=_ |- _ => rename x into c
  end.
  exists psi, phi. intros f. unfold phi. unfold psi. cbn. reflexivity.
Defined.

Lemma help (A B : Type) (f : A -> B) (x y : A) (e : x = y) :
  (transport (fun y : A => f x = f y) e id = ap f e o id)%type.
Proof. destruct e. reflexivity. Defined.

(** This is lemma 4.2.5 from the book. *)

Theorem fine (A B : Type) (f : A -> B) (y : B) (s t : fib _=_ f y) :
  (s = t) ~= {g : proj1_sig s = proj1_sig t |
  ap f g o proj2_sig s = proj2_sig t}%type.
Proof.
  eapply trans; try apply (sig_is_equiv_types s t).
  destruct s as [x p], t as [x' p']. cbn. subst y.
  hnf. pose (fun a : {g : x = x' | transport (fun y : A => f x = f y) g id%type = p'} =>
  (proj1_sig a; transport (fun p : _ => p = p') (help f (proj1_sig a)) (proj2_sig a)) :
  {g : x = x' | (ap f g o id)%type = p'}) as e.
  pose (fun a : {g : x = x' | (ap f g o id)%type = p'} =>
  (proj1_sig a; transport (fun p : _ => p = p') (help f (proj1_sig a) ^-1) (proj2_sig a)) :
  {g : x = x' | transport (fun y : A => f x = f y) g id%type = p'}) as e'.
  exists e. subst e. repeat (split; try typeclasses eauto).
  exists e'. subst e'. repeat (split; try typeclasses eauto).
  intros [e e']. cbn. apply ap.
  rewrite transport_trans. rewrite eq_trans_sym_inv_r.
  cbn. reflexivity.
  exists e'. subst e'. repeat (split; try typeclasses eauto).
  intros [e e']. cbn. apply ap.
  rewrite transport_trans. rewrite eq_trans_sym_inv_l.
  cbn. reflexivity.
Defined.

(** This is theorem 4.2.6 from the book. *)

Theorem curses (A B : Type) (f : A -> B) (y : B)
  `{!IsHAE f} : IsContr (fib _=_ f y) _=_.
Proof.
  match goal with
  | x : IsHAE _ |- _ => rename x into IHAE
  end.
  destruct IHAE as [g [II c]].
  unfold iso_l_is_proper_f in c. unfold iso_is_iso_l in c.
  destruct II as [[] []].
  hnf.
  set (s := (g y; sect (f := f) (g := g) y ^-1) : fib _=_ f y); cbn in s.
  exists s. intros t.
  pose proof fine s t as IET.
  apply sym in IET.
  apply (projT1 IET).
  subst s; destruct t as [x p].
  pose (retr (f := f)) as r.
  pose (sect (f := f)) as s.
  set (gamma := (r x o ap g p)%type).
  exists gamma. unfold proj2_sig. subst gamma. subst r.
  assert (c' : forall x : A, ap f (retr x) = sect (f x)).
  { intros x'. change @ap with @f_equal. apply (c x'). }
  rewrite ap_trans.
  rewrite p. rewrite ap_refl. rewrite eq_trans_refl_l.
  rewrite c'. rewrite eq_trans_sym_inv_l. reflexivity.
Defined.

Lemma move_this (A : Type)
  (x y : A) (p q : x = y) (c : (id = p o (q ^-1))%type) : q = p.
Proof.
  rewrite <- (eq_trans_sym_inv_l q) in c.
  apply HLevels.eq_trans_cancel in c.
  apply c.
Defined.

Lemma move_that (A : Type)
  (x y z : A) (p : x = y) (q : y = z) (r : x = z)
  (c : (q o p = r)%type) : (q = r o (p ^-1))%type.
Proof.
  destruct r.
  rewrite <- (eq_trans_sym_inv_r p) in c.
  apply HLevels.eq_trans_cancel in c.
  rewrite eq_trans_refl_r.
  apply c.
Defined.

(** This is lemma 2.4.3 from the book. *)

Lemma commuting (A B : Type)
  (f g : A -> B) (h : forall x : A, f x = g x) (x y : A) (e : x = y) :
  (ap g e o h x = h y o ap f e)%type.
Proof.
  destruct e. do 2 rewrite ap_refl.
  rewrite eq_trans_refl_l. rewrite eq_trans_refl_r. reflexivity.
Defined.

(** This is corollary 2.4.4 from the book. *)

Lemma commuting_harder (A : Type)
  (f : A -> A) (h : forall x : A, f x = id x) (x : A) :
  h (f x) = ap f (h x).
Proof.
  epose proof commuting h _ as c.
  rewrite ap_id in c.
  rewrite eq_trans_sym_inv_r in c.
  rewrite ap_sym in c.
  apply move_this in c.
  symmetry. apply c.
Defined.

(** This is theorem 4.2.3 from the book. *)

Lemma pre_unhae (A B : Type) (f : A -> B)
  `{!IsQInv _=_ _=_ f} : IsHAE f.
Proof.
  match goal with
  | x : IsQInv _ _ _ |- _ => rename x into IQI
  end.
  destruct IQI as [g [IIL IIR]].
  eset (II := _ : IsIso _=_ _=_ f g). Unshelve. 2:
  { split.
    - split.
      + apply is_proper_eq_1.
      + apply is_proper_eq_1.
      + intros x. apply retr.
    - split.
      + apply is_proper_eq_1.
      + apply is_proper_eq_1.
      + intros x.
        pose proof fun b : B => sect (f := f) (g := g) (f (g b)) ^-1 as s.
        pose proof fun b : B => ap f (retr (f := f) (g := g) (g b)) as r.
        pose proof fun b : B => sect (f := f) (g := g) b as t.
        pose proof fun b : B => (t b o r b o s b)%type as u.
        apply u. }
  hnf. exists g. exists II. subst II. intros x.
  unfold retr, sect, iso_l_is_retr, iso_r_is_sect, iso_is_iso_l, iso_is_iso_r.
  destruct IIL as [p p' r], IIR as [q q' s].
  change @f_equal with @ap.
  pose proof commuting (g := f) (fun y : A => s (f y)) (r x) as c.
  cbv beta in c. apply move_that in c. rewrite c. clear c.
  f_equal. f_equal.
  rewrite <- ap_ap. apply (f_equal (ap f)).
  symmetry. apply (commuting_harder (f := fun y => g (f y)) r).
Defined.

Lemma unhae (A B : Type) (f : A -> B)
  `{!IsBiInv _=_ _=_ f} : IsHAE f.
Proof.
  match goal with
  | x : IsBiInv _ _ _ |- _ => rename x into IBI
  end.
  apply @pre_unhae.
  apply bi_inv_is_q_inv.
Defined.

(** This is an approximation of theorem 4.2.6 from the book. *)

Theorem curses' (A B : Type) (f : A -> B) (y : B)
  `{!IsBiInv _=_ _=_ f} : IsContr (fib _=_ f y) _=_.
Proof.
  match goal with
  | x : IsBiInv _ _ _ |- _ => rename x into IBI
  end.
  apply curses. apply unhae.
Defined.

(** This is definition 4.7.5 from the book. *)

Definition total (A : Type) (P Q : A -> Prop)
  (f : forall x : A, P x -> Q x) (a : {x : A | P x}) : {x : A | Q x}.
Proof. apply (proj1_sig a; f (proj1_sig a) (proj2_sig a))%sig. Defined.

Definition total_ex (A : Type) (P Q : A -> Prop)
  (f : forall x : A, P x -> Q x) (a : exists x : A, P x) : exists x : A, Q x.
Proof. destruct a as [x p]. exists x. apply f. apply p. Defined.

Definition fibernator (A : Type) (P Q : A -> Prop)
  (f : forall x : A, P x -> Q x) (x : A) (q : Q x) :
  {a : {x : A | P x} | (x; q) = total f a} -> {p : P x | q = f x p}.
Proof.
  intros [[y p] e]. cbv in e.
  (* pose proof ap proj1_sig e as e'.
  cbv in e'.
  destruct e'.
  exists (transport P id%type p).
  rewrite transport_refl.
  *)
  inversion_sigma e as [e0 e1].
  destruct e0.
  cbv in e1.
  exists p. apply e1.
Defined.

Definition cofibernator (A : Type) (P Q : A -> Prop)
  (f : forall x : A, P x -> Q x) (x : A) (q : Q x) :
  {p : P x | q = f x p} -> {a : {x : A | P x} | (x; q) = total f a}.
Proof.
  intros [p e]. exists (x; p)%sig. cbv. f_equal. apply e.
Defined.

Arguments cofibernator {_ _ _} _ {_ _} _.

Lemma fibering (A : Type) (P Q : A -> Prop)
  (f : forall x : A, P x -> Q x) (x : A) (q : Q x) :
  IsBiInv _=_ _=_ (fibernator f (x := x) (q := q)).
Proof.
  split.
  - exists (cofibernator f (x := x) (q := q)).
    split; try apply is_proper_eq_1.
    intros [[y p] e]. cbv in e. inversion_sigma e as [e0 e1].
    destruct e0. cbv in e1. subst q. reflexivity.
  - exists (cofibernator f (x := x) (q := q)).
    split; try apply is_proper_eq_1.
    intros [p e]. subst q. reflexivity.
Defined.

(** This is theorem 4.7.6 from the book. *)

Lemma fiberwise (A : Type) (P Q : A -> Prop)
  (f : forall x : A, P x -> Q x) (x : A) (q : Q x) :
  fib _=_ (total f) (x; q) ~= fib _=_ (f x) q.
Proof.
  exists (fibernator f). apply fibering.
Defined.

Lemma contrequiv (A B : Type) (f : A -> B)
  `{!IsContr A _=_} `{!IsContr B _=_} :
  IsBiInv _=_ _=_ f.
Proof.
  destruct (@contr A _=_ _) as [x ex].
  destruct (@contr B _=_ _) as [y ey].
  split.
  - exists (const x).
    split; try apply is_proper_eq_1.
    intros z. cbv. apply ex.
  - exists (const x).
    split; try apply is_proper_eq_1.
    intros z. cbv. etransitivity. symmetry. apply ey. apply ey.
Defined.

(** This is definition 4.7.2 from the book. *)

Class IsRetrThings (X Y A B : Type) (f : X -> Y) (g : A -> B) : Type := {
  r : X -> A;
  s : A -> X;
  r' : Y -> B;
  s' : B -> Y;
  R (x : A) : r (s x) = x;
  R' (y : B) : r' (s' y) = y;
  L (x : A) : f (s x) = s' (g x);
  K (z : X) : g (r z) = r' (f z);
  H (a : A) : g (r (s a)) = r' (s' (g a));
}.

(** This is theorem 4.7.4 from the book. *)

Lemma equiv_ret (A B C D : Type)
  (f : A -> B) (g : C -> D) :
  IsRetrThings f g -> IsBiInv _=_ _=_ f -> IsBiInv _=_ _=_ g.
Proof.
  intros [] [[? [_ _ ?]] [? [_ _ ?]]]. hnf in *. split.
  hnf. exists (r0 o x o s'0).
  split; try apply is_proper_eq_1. intros z. cbv.
  rewrite <- L0. rewrite iso_l_is_retr. rewrite R0. reflexivity.
  hnf. exists (r0 o x0 o s'0).
  split; try apply is_proper_eq_1. intros z. cbv.
  rewrite K0. rewrite iso_r_is_sect. rewrite R'0. reflexivity.
Defined.

(** This is theorem 4.7.7 from the book. *)

Lemma fiberwise_transform (A : Type) (P Q : A -> Prop)
  (f : forall x : A, P x -> Q x) (x : A) :
  IsBiInv _=_ _=_ (f x) -> IsBiInv _=_ _=_ (total f).
Proof.
  eapply equiv_ret. esplit. Unshelve.
  8: { intros q. exists x. apply q. }
  6: { intros p. exists x. apply p. }
Admitted.

Lemma fiberwise_transform_dual (A : Type) (P Q : A -> Prop)
  (f : forall x : A, P x -> Q x) (x : A) :
  IsBiInv _=_ _=_ (total f) -> IsBiInv _=_ _=_ (f x).
Proof.
  eapply equiv_ret. esplit. Unshelve.
  9: { intros q. exists x. apply q. }
  7: { intros p. exists x. apply p. }
Admitted.

(** This is theorem 4.9.4 from the book. *)

Lemma eq_pi_contr (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x) _=_} : IsContr (forall x : A, P x) _=_.
Proof.
  match goal with
  | h : forall _ : _, IsContr _ _=_ |- _ => rename h into c
  end.
  pose proof why_squared as w.
  pose proof eq_pi_is_what as q.
  pose proof @ret (fib _=_ alpha id%core) (forall x : A, P x) q as r.
  apply r.
  apply curses'.
  apply after_why_squared.
Defined.

(** This is theorem 4.9.5 from the book. *)

Lemma conclusion (A : Type) (P : A -> Prop) (f g : forall x : A, P x) :
  IsBiInv _=_ _=_ (happly f g).
Proof.
  (* enough (theorem_4_7_7 :
  IsBiInv _=_ _=_ (fun a : exists g : forall x : A, P x, f = g =>
  match a with
  | (x; e)%ex => (x; happly _ _ e)%ex
  end :
  exists h : forall x : A, P x, forall x : A, f x = h x)) by admit. *)
  enough (by_theorem_4_7_7 :
  IsBiInv _=_ _=_ (total (happly f))).
  { epose proof @fiberwise_transform_dual _ _ _ (happly f) as t.
    eapply t. apply by_theorem_4_7_7. }
  enough (by_theorem_3_11_8 :
  IsContr {h : forall x : A, P x | forall x : A, f x = h x} _=_).
  (** Equivalence preserves contractibility. *)
  { epose proof @curses' _ _ as b.
    epose proof @ret _ _ as r. unfold IsRetrType in r.
    epose proof @fiberwise_transform _ _ _ (happly f) as t.
    admit. }
  enough (by_theorem_2_15_7 :
  IsContr (forall x : A, {a : P x | f x = a}) _=_).
  { epose proof @seriously A P (fun (a : A) (b : P a) => f a = b) as s; cbv beta in s.
    rewrite <- (ua s). assumption. }
  apply @eq_pi_contr.
  intros x. apply @sig_contr.
  (** This would require some effort. *)
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

(** Proposition extensionality
    makes function extensionality an equality. *)

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
  `{!forall x : A, IsContr (P x) _=_} : IsContr (forall x : A, P x) _=_.
Proof.
  match goal with
  | h : forall _ : _, IsContr _ _=_ |- _ => rename h into c
  end.
  apply @inhabited_prop_is_contr.
  - intros x. apply c.
  - apply (@eq_pi_is_prop _). intros x. apply contr_is_prop.
Qed.

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

(** Univalence implies proposition extensionality for types. *)

#[export] Instance univ_is_prop_ext_type `{IsUniv} : IsPropExtType.
Proof.
  intros A B IPA IPB [f g]. pose proof univ_is_bi_inv A B as s.
  destruct s as [ua [IPidtoeqv IPua]]. apply ua. exists f. split.
  - exists g. split; try typeclasses eauto. intros x. apply irrel.
  - exists g. split; try typeclasses eauto. intros x. apply irrel.
Qed.

(** We cannot prove that [IsPropExt] and [IsPropExtType] are related,
    because [Prop] and [Type] are stratified. *)

Module FromAxioms.

#[export] Instance is_prop_ext : IsPropExt.
Proof. intros A B. apply propositional_extensionality. Qed.

#[export] Instance is_prop_ext_type : IsPropExtType.
Proof. intros A B. apply propositional_extensionality_type. Qed.

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
