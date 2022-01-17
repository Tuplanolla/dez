(** * Groupoid Structure *)

From Coq Require Import
  Logic.ProofIrrelevance.
From DEZ.Has Require Export
  Decisions.
From DEZ.Is Require Export
  Reflexive Symmetric Transitive Equivalence.
From DEZ.ShouldHave Require Import
  EquivalenceNotations.

#[local] Unset Universe Minimization ToSet.

#[local] Open Scope type_scope.

(** ** Contractibility *)
(** ** Singleton *)

Class IsContr (A : Type) (X : A -> A -> Prop) : Prop :=
  contr : exists x : A, forall y : A, X x y.

Class IsContrEq (A : Type) : Prop :=
  contr_eq : exists x : A, forall y : A, x = y.

Section Context.

Context (A : Type).

#[local] Instance is_contr_eq_is_contr `{IsContrEq A} : @IsContr A _=_.
Proof. exact contr_eq. Qed.

#[local] Instance is_contr_is_contr_eq `{!@IsContr A _=_} : IsContrEq A.
Proof. exact contr. Qed.

End Context.

(** ** Proof Irrelevance *)
(** ** Proposition *)

Class IsProp (A : Type) (X : A -> A -> Prop) : Prop :=
  irrel (x y : A) : X x y.

Class IsPropEq (A : Type) : Prop :=
  irrel_eq (x y : A) : x = y.

Section Context.

Context (A : Type).

#[local] Instance is_prop_eq_is_prop `{IsPropEq A} : @IsProp A _=_.
Proof. exact irrel_eq. Qed.

#[local] Instance is_prop_is_prop_eq `{!@IsProp A _=_} : IsPropEq A.
Proof. exact irrel. Qed.

End Context.

(** ** Set *)
(** ** Uniqueness of Identity Proofs *)

Fail Fail Class IsSetEq (A : Type) : Prop :=
  uip_eq (x y : A) (a b : x = y) : a = b.

Arguments uip {_ _} _ _ _ _.

Notation IsSetEq := UIP.
Notation uip_eq := (uip : IsSetEq _).

Class IsSet (A : Type) (X : A -> A -> Prop)
  (Y : forall {x y : A}, X x y -> X x y -> Prop) : Prop :=
  uip (x y : A) (a b : X x y) : Y a b.

Section Context.

Context (A : Type).

Let X (x y : A) (a b : x = y) := a = b.

#[local] Instance is_set_eq_is_set `{!IsSetEq A} : @IsSet A _=_ (@X).
Proof. exact uip_eq. Qed.

#[local] Instance is_set_is_set_eq `{!@IsSet A _=_ (@X)} : IsSetEq A.
Proof. exact uip. Qed.

End Context.

(** ** Homotopy [(2 + n)]-Type *)
(** ** Type of Homotopy Level [n] *)

(** For the sake of convenience, we count up from [0],
    even though homotopy levels conventionally count up from [-2]. *)

Inductive IsHLevel (A : Type) (X : forall {A : Type}, A -> A -> Prop) :
  nat -> Prop :=
  | h_level_zero `{!@IsContr A X} : IsHLevel A (@X) O
  | h_level_succ (n : nat)
    `{forall x y : A, IsHLevel (X x y) (@X) n} : IsHLevel A (@X) (S n).

Existing Class IsHLevel.

Inductive IsHLevelEq (A : Type) : nat -> Prop :=
  | h_level_eq_zero `{IsContrEq A} : IsHLevelEq A O
  | h_level_eq_succ (n : nat)
    `{forall x y : A, IsHLevelEq (x = y) n} : IsHLevelEq A (S n).

Existing Class IsHLevelEq.

Section Context.

Context (A : Type) (n : nat).

Let X (A : Type) (x y : A) := x = y.

#[local] Instance is_h_level_eq_is_h_level
  `{IsHLevelEq A n} : IsHLevel A (@X) n.
Proof.
  match goal with
  | h : IsHLevelEq _ _ |- _ => rename h into a
  end.
  revert A X a. induction n as [| p b]; intros A X a.
  - constructor. inversion_clear a. eauto.
  - constructor. intros x y. inversion_clear a as [| ? c].
    pose proof (c x y) as d. eauto. Qed.

#[local] Instance is_h_level_is_h_level_eq
  `{!@IsHLevel A (@X) n} : IsHLevelEq A n.
Proof.
  match goal with
  | h : IsHLevel _ _ _ |- _ => rename h into a
  end.
  revert A X a. induction n as [| p b]; intros A X a.
  - constructor. inversion_clear a. eauto.
  - constructor. intros x y. inversion_clear a as [| ? c].
    pose proof (c x y) as d. eauto. Qed.

End Context.

(** Inversion of [h_level_zero]. *)

#[local] Instance is_h_level_is_contr
  (A : Type) (X : forall {A : Type}, A -> A -> Prop)
  `{IsHLevel A (@X) O} : @IsContr A X.
Proof.
  match goal with
  | h : IsHLevel _ _ _ |- _ => rename h into a
  end. inversion_clear a. eauto. Qed.

#[bad]
#[local] Instance h_level_contr_eq (A : Type) `(IsHLevelEq A 0) : IsContrEq A.
Proof. inversion_clear H. eauto. Qed.

(** Biconditionality of [h_level_zero]. *)

Lemma iff_is_h_level_is_contr
  (A : Type) (X : forall {A : Type}, A -> A -> Prop) :
  IsHLevel A (@X) O <-> @IsContr A X.
Proof.
  split.
  - intros a. apply is_h_level_is_contr.
  - apply h_level_zero. Qed.

#[bad]
#[local] Instance contr_eq_h_level (A : Type) `(IsContrEq A) : IsHLevelEq A 0.
Proof. apply h_level_eq_zero. Qed.

(** Inversion of [h_level_succ]. *)

#[local] Instance is_h_level_succ_is_h_level_eqv
  (A : Type) (X : forall {A : Type}, A -> A -> Prop) (n : nat)
  `{IsHLevel A (@X) (S n)} (x y : A) : IsHLevel (X x y) (@X) n.
Proof.
  match goal with
  | h : IsHLevel _ _ _ |- _ => rename h into a
  end. inversion_clear a. eauto. Qed.

#[bad]
#[local] Instance h_level_eq_succ_h_level_eq (A : Type) (n : nat)
  `{IsHLevelEq A (S n)} (x y : A) : IsHLevelEq (x = y) n.
Proof.
  match goal with
  | s : IsHLevelEq _ _ |- _ => inversion_clear s
  end. eauto. Qed.

(** Biconditionality of [h_level_succ]. *)

Lemma iff_is_h_level_succ_is_h_level_eqv
  (A : Type) (X : forall {A : Type}, A -> A -> Prop) (n : nat) :
  IsHLevel A (@X) (S n) <-> forall x y : A, IsHLevel (X x y) (@X) n.
Proof.
  split.
  - intros a. apply is_h_level_succ_is_h_level_eqv.
  - intros a. apply h_level_succ. Qed.

#[bad] Lemma iff_h_level_eq_succ_h_level_eq
  (A : Type) (n : nat) :
  IsHLevelEq A (S n) <-> forall x y : A, IsHLevelEq (x = y) n.
Proof.
  split.
  - intros a. apply h_level_eq_succ_h_level_eq.
  - intros a. apply h_level_eq_succ. Qed.

(** Successive homotopy levels are cumulative. *)

#[local] Instance is_h_level_is_h_level_succ
  (A : Type) (X : forall {A : Type}, A -> A -> Prop) (n : nat)
  `{forall {A : Type}, @IsEq A X} `{IsHLevel A (@X) n} : IsHLevel A (@X) (S n).
Proof.
  match goal with
  | h : forall _, IsEq _, i : IsHLevel _ _ _ |- _ => rename h into a; rename i into b
  end.
  revert A X a b. induction n as [| p c]; intros A X a b.
  - apply iff_is_h_level_is_contr in b. destruct b as [x f].
    apply iff_is_h_level_succ_is_h_level_eqv.
    intros y z. apply h_level_zero. exists (trans _ _ _ (sym _ _ (f y)) (f z)).
    intros c. (** This requires J. *) admit.
  - constructor. intros x y. apply c. eauto.
    apply is_h_level_succ_is_h_level_eqv. Abort.

#[bad]
Lemma h_level_h_level_eq_succ (A : Type) (n : nat) `(IsHLevelEq A n) : IsHLevelEq A (S n).
Proof.
  match goal with
  | h : IsHLevelEq _ _ |- _ => induction h as [A [x a] | n A t t']
  end.
  - apply iff_h_level_eq_succ_h_level_eq.
    intros y z. apply contr_eq_h_level. exists (a z o a y ^-1).
    intros c. rewrite c.
    unfold symmetry, eq_Symmetric, transitivity, eq_Transitive.
    rewrite eq_trans_sym_inv_l. reflexivity.
  - apply h_level_eq_succ. Qed.

(** Contractibility is equivalent to truncation at level [-2]. *)

#[bad]
Lemma iff_contr_eq_h_level (A : Type) : IsContrEq A <-> IsHLevelEq A 0.
Proof. split; [apply contr_eq_h_level | apply h_level_contr_eq]. Qed.

Lemma prop_h_level (A : Type) `(IsPropEq A) : IsHLevelEq A 1.
Proof.
  apply iff_h_level_eq_succ_h_level_eq.
  intros x y. apply iff_contr_eq_h_level.
  exists (irrel_eq x y o irrel_eq x x ^-1). intros a.
  rewrite a. rewrite eq_trans_sym_inv_l. reflexivity. Qed.

Lemma h_level_prop (A : Type) `(IsHLevelEq A 1) : IsPropEq A.
Proof.
  match goal with
  | h : IsHLevelEq _ _ |- _ => inversion_clear h
  end.
  intros x y.
  assert (a : IsContrEq (x = y)).
  { apply iff_contr_eq_h_level. auto. }
  apply a. Qed.

(** Proof irrel_eqevance is equivalent to truncation at level [-1]. *)

Lemma iff_prop_h_level (A : Type) : IsPropEq A <-> IsHLevelEq A 1.
Proof. split; [apply prop_h_level | apply h_level_prop]. Qed.

Lemma set_h_level (A : Type) `(IsSetEq A) : IsHLevelEq A 2.
Proof.
  apply iff_h_level_eq_succ_h_level_eq.
  intros x y. apply iff_prop_h_level.
  intros a b. apply uip_eq. Qed.

Lemma h_level_set (A : Type) `(IsHLevelEq A 2) : IsSetEq A.
Proof.
  match goal with
  | h : IsHLevelEq _ _ |- _ => inversion_clear h
  end.
  intros x y.
  assert (a : IsPropEq (x = y)).
  { apply iff_prop_h_level. auto. }
  apply a. Qed.

(** Uniqueness of identity proofs is equivalent to truncation at level [0]. *)

Lemma iff_set_h_level (A : Type) : IsSetEq A <-> IsHLevelEq A 2.
Proof. split; [apply set_h_level | apply h_level_set]. Qed.

(** Hints that construct truncations. *)

Create HintDb trunc.

#[export] Hint Resolve h_level_eq_zero h_level_eq_succ h_level_h_level_eq_succ
  contr_eq_h_level prop_h_level set_h_level : trunc.

(** Hints that eliminate truncations. *)

Create HintDb untrunc.

#[export] Hint Resolve h_level_eq_succ_h_level_eq h_level_h_level_eq_succ
  h_level_contr_eq h_level_prop h_level_set : untrunc.

Lemma prop_contr_eq_eq (A : Type) `(IsPropEq A) (x y : A) : IsContrEq (x = y).
Proof. eauto 7 with trunc untrunc. Qed.

Lemma contr_eq_eq_prop (A : Type) `(forall x y : A, IsContrEq (x = y)) : IsPropEq A.
Proof. eauto 7 with trunc untrunc. Qed.

(** Proof irrel_eqevance is equivalent
    to contr_eqactibility of identity proofs. *)

Lemma iff_prop_contr_eq_eq (A : Type) :
  IsPropEq A <-> forall x y : A, IsContrEq (x = y).
Proof.
  split; [apply prop_contr_eq_eq | apply contr_eq_eq_prop] ||
  split; eauto 7 with trunc untrunc. Qed.

Lemma set_prop_eq (A : Type) `(IsSetEq A) (x y : A) : IsPropEq (x = y).
Proof. eauto 7 with trunc untrunc. Qed.

Lemma prop_eq_set (A : Type)
  `(forall x y : A, IsPropEq (x = y)) (x y : A) : IsSetEq A.
Proof. eauto 7 with trunc untrunc. Qed.

(** Uniqueness of identity proofs is equivalent
    to proof irrel_eqevance of identity proofs. *)

Lemma iff_set_prop_eq (A : Type) : IsSetEq A <-> forall x y : A, IsPropEq (x = y).
Proof.
  split; [apply set_prop_eq | apply prop_eq_set] ||
  split; eauto 7 with trunc untrunc. Qed.

(** Contractibility implies proof irrel_eqevance. *)

Lemma contr_eq_prop (A : Type) `(IsContrEq A) : IsPropEq A.
Proof. eauto 7 with trunc untrunc. Qed.

(** Proof irrel_eqevance implies uniqueness of identity proofs. *)

Lemma prop_set (A : Type) `(IsPropEq A) : IsSetEq A.
Proof. eauto 7 with trunc untrunc. Qed.

#[export] Hint Resolve prop_contr_eq_eq set_prop_eq
  contr_eq_prop prop_set : typeclass_instances.

(** True propositions are contr_eqactible. *)

Lemma prop_contr_eq (A : Type) (x : A) `(IsPropEq A) : IsContrEq A.
Proof. exists x. apply irrel_eq. Qed.

(** TODO Clean up. *)

From Coq Require Import
  Logic.FunctionalExtensionality Logic.PropExtensionality.
From DEZ.Is Require Import
  Extensional.
From Equations.Prop Require Import
  Logic.

Lemma is_contr_eq_is_prop `(IsFunExtDep) (A : Prop) : IsPropEq (IsContrEq A).
Proof.
  intros x y.
  assert (z : IsPropEq A).
  { apply contr_eq_prop. apply x. }
  assert (w : IsSetEq A).
  { apply prop_set. apply z. }
  destruct x as [x a], y as [y b].
  apply eq_ex with (a y).
  assert (IsPropEq (forall z : A, y = z)).
  intros u v. apply fun_ext_dep. intros t. apply irrel_eq.
  eapply irrel_eq. Qed.

Lemma is_contr_eq_is_contr_eq `(IsFunExtDep) (A : Prop) `(IsContrEq A) :
  IsContrEq (IsContrEq A).
Proof.
  apply prop_contr_eq.
  - assumption.
  - apply is_contr_eq_is_prop. assumption. Qed.

Lemma pi_is_prop `(IsFunExtDep) (A : Type) (P : A -> Type)
  `(forall x : A, IsPropEq (P x)) : IsPropEq (forall x : A, P x).
Proof.
  rename H0 into h.
  unfold IsPropEq in *.
  intros f g.
  apply fun_ext_dep.
  intros x.
  specialize (h x (f x) (g x)).
  apply h. Qed.

Lemma pi_is_contr_eq `(IsFunExtDep) (A : Type) (P : A -> Prop)
  `(forall x : A, IsContrEq (P x)) : IsContrEq (forall x : A, P x).
Proof.
  assert (forall x : A, IsPropEq (P x)).
  { intros x. apply contr_eq_prop. apply H0. }
  apply pi_is_prop in H1; try eauto.
  apply prop_contr_eq.
  - intros x. pose proof H0 x. destruct H2. assumption.
  - assumption. Qed.

Lemma pi_is_set `(IsPropExt) `(IsFunExtDep) (A : Type) (P : A -> Type)
  `(forall x : A, IsSetEq (P x)) : IsSetEq (forall x : A, P x).
Proof.
  rename H1 into h.
  pose proof fun (x : A) (a b : P x) =>
  set_prop_eq (h x) (x := a) (y := b) as h'.
  intros f g.
  pose proof fun x : A => h' x (f x) (g x) as k.
  pose proof pi_is_prop _ k as k'. cbv beta in k'.
  enough (IsPropEq (f = g)) by auto.
  pose proof (equal_f_dep (f := f) (g := g)) as l.
  pose proof (fun_ext_dep (f := f) (g := g)) as r.
  pose proof conj l r as e.
  pose proof prop_ext e as w.
  rewrite w. apply k'. Qed.

Module FromAxioms.

#[local] Instance is_prop (A : Prop) : IsPropEq A.
Proof.
  intros x y.
  apply proof_irrelevance. Qed.

#[export] Hint Resolve is_prop : typeclass_instances.

End FromAxioms.

Lemma h_level_pi `(IsPropExt) `(IsFunExtDep) (A : Type) (P : A -> Prop) (n : nat)
  `(forall x : A, IsHLevelEq (P x) n) : IsHLevelEq (forall x : A, P x) n.
Proof.
  revert A P H1.
  induction n as [| p t]; intros A P H1.
  - pose proof fun x : A => h_level_contr_eq (H1 x).
    apply iff_contr_eq_h_level.
    apply (@pi_is_contr_eq H0 A P). apply H2.
  - apply (@h_level_eq_succ).
    intros f g.
    pose proof fun (x : A) a b =>
    h_level_eq_succ_h_level_eq (A := P x) (n := p) (H := H1 x) a b as u.
    pose proof fun_ext_dep (f := f) (g := g) as q.
    pose proof equal_f_dep (f := f) (g := g) as r.
    pose proof conj q r as w.
    pose proof prop_ext w.
    rewrite <- H2. apply t. intros x. apply h_level_eq_succ_h_level_eq. Qed.

#[local] Instance bool_is_set : IsSetEq bool.
Proof. intros x y a b. apply EqDec.eqdec_uip. apply bool_EqDec. Qed.

(** Let us write something extra dubious! *)

Definition lep (x y : bool) : Prop := x -> y.

Definition decreasing (f : nat -> bool) : Prop :=
  forall i : nat, lep (f (S i)) (f i).

Definition nat_inf : Type := {f : nat -> bool | decreasing f}.

Definition zero_inf : nat_inf.
Proof.
  exists (const false). intros i y. apply y. Defined.

Definition succ_inf (x : nat_inf) : nat_inf.
Proof.
  destruct x as [f a].
  exists (fun n : nat =>
  match n with
  | O => true
  | S p => f n
  end). intros i. revert f a. induction i as [| j b]; intros f a.
  - intros y. reflexivity.
  - intros y. apply a. apply y. Defined.

Fixpoint under (n : nat) : nat_inf :=
  match n with
  | O => zero_inf
  | S p => succ_inf (under p)
  end.

Definition LPO : Type :=
  forall x : nat_inf, HasDec (exists n : nat, x = under n).

Unset Universe Checking.

Lemma cohedberg `(IsPropExt) `(IsFunExtDep) :
  ~ forall (A : Type) `(IsSetEq A), HasEqDec A.
Proof.
  intros f.
  pose proof f (nat -> bool) as g.
  assert (x : IsSetEq (nat -> bool)).
  apply (pi_is_set _ _). intros _. apply (@bool_is_set).
  pose proof g x as h.
  clear f g x.
  (** Metatheoretical contr_eqadiction! *) Abort.
