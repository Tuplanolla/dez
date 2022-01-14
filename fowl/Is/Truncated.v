(** * Groupoid Structure *)

From Coq Require Import
  Logic.ProofIrrelevance.
From DEZ.Has Require Export
  Decisions.

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

#[export] Instance is_contr_is_contr_eq `{!@IsContr A _=_} : IsContrEq A.
Proof. exact contr. Qed.

#[export] Instance is_contr_eq_is_contr `{IsContrEq A} : @IsContr A _=_.
Proof. exact contr_eq. Qed.

End Context.

(** ** Proof Irrelevance *)
(** ** Proposition *)

Class IsProp (A : Type) (X : A -> A -> Prop) : Prop :=
  irrel (x y : A) : X x y.

Class IsPropEq (A : Type) : Prop :=
  irrel_eq (x y : A) : x = y.

Section Context.

Context (A : Type).

#[local] Instance is_prop_is_prop_eq `{!@IsProp A _=_} : IsPropEq A.
Proof. exact irrel. Qed.

#[local] Instance is_prop_eq_is_prop `{IsPropEq A} : @IsProp A _=_.
Proof. exact irrel_eq. Qed.

End Context.

(** ** Set *)
(** ** Uniqueness of Identity Proofs *)

Fail Fail Class IsSetEq (A : Type) : Prop :=
  uip_eq (x y : A) (a b : x = y) : a = b.

Notation IsSetEq := UIP.
Notation uip_eq := uip.

Arguments uip_eq {_ _} _ _ _ _.

Class IsSet (A : Type) (X : A -> A -> Prop)
  (Y : forall {x y : A}, X x y -> X x y -> Prop) : Prop :=
  uip (x y : A) (a b : X x y) : Y a b.

Section Context.

Context (A : Type).

Let X (x y : A) (a b : x = y) := a = b.

#[local] Instance is_set_is_set_eq `{!@IsSet A _=_ (@X)} : IsSetEq A.
Proof. exact uip. Qed.

#[local] Instance is_set_eq_is_set `{!IsSetEq A} : @IsSet A _=_ (@X).
Proof. exact uip_eq. Qed.

End Context.

(** ** Homotopy [n]-Type *)
(** ** [n]-Truncation *)

(** For the sake of convenience, this type counts up from [0],
    even though truncation levels conventionally count up from [-2]. *)

Inductive IsTrunc (A : Type) (X : forall {A : Type}, A -> A -> Prop) :
  nat -> Prop :=
  | trunc_zero `{!@IsContr A X} : IsTrunc A (@X) O
  | trunc_succ (n : nat)
    `{forall x y : A, IsTrunc (X x y) (@X) n} : IsTrunc A (@X) (S n).

Existing Class IsTrunc.

Arguments trunc_zero {_} _.
Arguments trunc_succ {_ _} _.

Inductive IsTruncEq (A : Type) : nat -> Prop :=
  | trunc_eq_zero `{IsContrEq A} : IsTruncEq A O
  | trunc_eq_succ (n : nat)
    `{forall x y : A, IsTruncEq (x = y) n} : IsTruncEq A (S n).

Existing Class IsTruncEq.

Arguments trunc_eq_zero {_} _.
Arguments trunc_eq_succ {_ _} _.

Section Context.

Context (A : Type) (n : nat).

Let X (A : Type) (x y : A) := x = y.

#[local] Instance is_trunc_is_trunc_eq `{!@IsTrunc A (@X) n} : IsTruncEq A n.
Proof.
  match goal with
  | h : IsTrunc _ _ _ |- _ => rename h into a
  end.
  remember (@X) as Y eqn : r. induction a as [A Y a | A Y n a b].
  - subst X Y. apply trunc_eq_zero. eauto.
  - subst X Y. apply trunc_eq_succ. eauto. Qed.

#[local] Instance is_trunc_eq_is_trunc `{IsTruncEq A n} : IsTrunc A (@X) n.
Proof.
  match goal with
  | h : IsTruncEq _ _ |- _ => rename h into a
  end.
  revert A X a. induction n as [| p b]; intros A X a.
  - apply trunc_zero. inversion_clear a. eauto.
  - apply trunc_succ. intros x y. inversion_clear a as [| ? c].
    pose proof (c x y) as d. eauto. Qed.

End Context.

(** Inversion principle for [trunc_eq_succ]. *)

Lemma trunc_succ_trunc (A : Type) (X : forall {A : Type}, A -> A -> Prop)
  (n : nat) `{IsTrunc A (@X) (S n)} (x y : A) : IsTrunc (X x y) (@X) n.
Proof.
  match goal with
  | s : IsTrunc _ _ _ |- _ => inversion_clear s
  end. eauto. Qed.

Arguments is_trunc_is_trunc_eq {_ _} _.

Lemma trunc_eq_succ_trunc_eq (A : Type) (n : nat)
  `{IsTruncEq A (S n)} (x y : A) : IsTruncEq (x = y) n.
Proof. eapply is_trunc_is_trunc_eq.
  match goal with
  | s : IsTruncEq _ _ |- _ => inversion_clear s
  end. eauto. Qed.

(** Truncation at the next level is equivalent to truncation of identities. *)

Lemma iff_trunc_eq_succ_trunc_eq (A : Type) (n : nat) :
  IsTruncEq A (S n) <-> forall x y : A, IsTruncEq (x = y) n.
Proof. split; [apply trunc_eq_succ_trunc_eq | apply trunc_eq_succ]. Qed.

(** Truncation is cumulative. *)

Lemma trunc_trunc_eq_succ (A : Type) (n : nat) `(IsTruncEq A n) : IsTruncEq A (S n).
Proof.
  match goal with
  | t : IsTruncEq _ _ |- _ => induction t as [A [x a] | n A t t']
  end.
  - apply iff_trunc_eq_succ_trunc_eq.
    intros y z. apply trunc_eq_zero. exists (a z o a y ^-1).
    intros c. rewrite c. rewrite eq_trans_sym_inv_l. reflexivity.
  - apply trunc_eq_succ. auto. Qed.

Lemma contr_eq_trunc (A : Type) `(IsContrEq A) : IsTruncEq A 0.
Proof. apply trunc_eq_zero. auto. Qed.

Lemma trunc_contr_eq (A : Type) `(IsTruncEq A 0) : IsContrEq A.
Proof.
  match goal with
  | t : IsTruncEq _ _ |- _ => inversion_clear t
  end. auto. Qed.

(** Contractibility is equivalent to truncation at level [-2]. *)

Lemma iff_contr_eq_trunc (A : Type) : IsContrEq A <-> IsTruncEq A 0.
Proof. split; [apply contr_eq_trunc | apply trunc_contr_eq]. Qed.

Lemma prop_trunc (A : Type) `(IsPropEq A) : IsTruncEq A 1.
Proof.
  apply iff_trunc_eq_succ_trunc_eq.
  intros x y. apply iff_contr_eq_trunc.
  exists (irrel_eq x y o irrel_eq x x ^-1). intros a.
  rewrite a. rewrite eq_trans_sym_inv_l. reflexivity. Qed.

Lemma trunc_prop (A : Type) `(IsTruncEq A 1) : IsPropEq A.
Proof.
  match goal with
  | t : IsTruncEq _ _ |- _ => inversion_clear t
  end.
  intros x y.
  assert (a : IsContrEq (x = y)).
  { apply iff_contr_eq_trunc. auto. }
  apply a. Qed.

(** Proof irrel_eqevance is equivalent to truncation at level [-1]. *)

Lemma iff_prop_trunc (A : Type) : IsPropEq A <-> IsTruncEq A 1.
Proof. split; [apply prop_trunc | apply trunc_prop]. Qed.

Lemma set_trunc (A : Type) `(IsSetEq A) : IsTruncEq A 2.
Proof.
  apply iff_trunc_eq_succ_trunc_eq.
  intros x y. apply iff_prop_trunc.
  intros a b. apply uip_eq. Qed.

Lemma trunc_set (A : Type) `(IsTruncEq A 2) : IsSetEq A.
Proof.
  match goal with
  | t : IsTruncEq _ _ |- _ => inversion_clear t
  end.
  intros x y.
  assert (a : IsPropEq (x = y)).
  { apply iff_prop_trunc. auto. }
  apply a. Qed.

(** Uniqueness of identity proofs is equivalent to truncation at level [0]. *)

Lemma iff_set_trunc (A : Type) : IsSetEq A <-> IsTruncEq A 2.
Proof. split; [apply set_trunc | apply trunc_set]. Qed.

(** Hints that construct truncations. *)

Create HintDb trunc.

#[export] Hint Resolve trunc_eq_zero trunc_eq_succ trunc_trunc_eq_succ
  contr_eq_trunc prop_trunc set_trunc : trunc.

(** Hints that eliminate truncations. *)

Create HintDb untrunc.

#[export] Hint Resolve trunc_eq_succ_trunc_eq trunc_trunc_eq_succ
  trunc_contr_eq trunc_prop trunc_set : untrunc.

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
  apply pi_is_prop in H1; try typeclasses eauto.
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

Lemma trunc_pi `(IsPropExt) `(IsFunExtDep) (A : Type) (P : A -> Prop) (n : nat)
  `(forall x : A, IsTruncEq (P x) n) : IsTruncEq (forall x : A, P x) n.
Proof.
  revert A P H1.
  induction n as [| p t]; intros A P H1.
  - pose proof fun x : A => trunc_contr_eq (H1 x).
    apply iff_contr_eq_trunc.
    apply (@pi_is_contr_eq H0 A P). apply H2.
  - apply trunc_eq_succ.
    intros f g.
    pose proof fun (x : A) a b =>
    trunc_eq_succ_trunc_eq (A := P x) (n := p) (H1 x) a b as u.
    pose proof fun_ext_dep (f := f) (g := g) as q.
    pose proof equal_f_dep (f := f) (g := g) as r.
    pose proof conj q r as w.
    pose proof prop_ext w.
    rewrite <- H2. apply t. intros x. apply trunc_eq_succ_trunc_eq. apply H1. Qed.

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
