(** * Groupoid Structure *)

From Coq Require Import
  Logic.ProofIrrelevance.
From DEZ.Has Require Export
  Decidability.
From DEZ.Is Require Export
  Isomorphism.

Unset Universe Minimization ToSet.

#[local] Open Scope type_scope.

(** ** Contractibility *)
(** ** Singleton *)

Class IsContrGen (A B : Type) (X : A -> B -> Prop) : Prop :=
  contr_gen : exists x : A, forall y : B, X x y.

Class IsContr (A : Type) : Prop :=
  contr : exists x : A, forall y : A, x = y.

(** ** Proof Irrelevance *)
(** ** Proposition *)

Class IsPropGen (A B : Type) (X : A -> B -> Prop) : Prop :=
  irrel_gen (x : A) (y : B) : X x y.

Class IsProp (A : Type) : Prop :=
  irrel (x y : A) : x = y.

(** ** Set *)
(** ** Uniqueness of Identity Proofs *)

Class IsSetGen (A B : Type) (X : A -> B -> Prop)
  (S : forall {x : A} {y : B}, X x y -> X x y -> Prop) : Prop :=
  uip_gen (x : A) (y : B) (a b : X x y) : S a b.

Fail Fail Class IsSet (A : Type) : Prop :=
  uip (x y : A) (a b : x = y) : a = b.

Notation IsSet := UIP.

Arguments uip {_ _ _ _} _ _.

(** ** Homotopy [n]-Type *)
(** ** [n]-Truncation *)

(** While this type is indexed over [nat], which starts from [0],
    the truncation levels actually start from [-2]. *)

Inductive IsTrunc (A : Type) : nat -> Prop :=
  | trunc_zero `(IsContr A) : IsTrunc A O
  | trunc_succ (n : nat)
    `(forall x y : A, IsTrunc (x = y) n) : IsTrunc A (S n).

Existing Class IsTrunc.

Lemma trunc_succ_trunc_eq (A : Type) (n : nat)
  `(IsTrunc A (S n)) (x y : A) : IsTrunc (x = y) n.
Proof.
  match goal with
  | t : IsTrunc _ _ |- _ => inversion_clear t
  end. eauto. Qed.

(** Truncation at the next level is equivalent to truncation of identities. *)

Lemma iff_trunc_succ_trunc_eq (A : Type) (n : nat) :
  IsTrunc A (S n) <-> forall x y : A, IsTrunc (x = y) n.
Proof. split; [apply trunc_succ_trunc_eq | apply trunc_succ]. Qed.

(** Truncation is cumulative. *)

Lemma trunc_trunc_succ (A : Type) (n : nat) `(IsTrunc A n) : IsTrunc A (S n).
Proof.
  match goal with
  | t : IsTrunc _ _ |- _ => induction t as [A [x a] | n A t t']
  end.
  - apply iff_trunc_succ_trunc_eq.
    intros y z. apply trunc_zero. exists (a z o a y ^-1).
    intros c. rewrite c. rewrite eq_trans_sym_inv_l. reflexivity.
  - apply trunc_succ. auto. Qed.

Lemma contr_trunc (A : Type) `(IsContr A) : IsTrunc A 0.
Proof. apply trunc_zero. auto. Qed.

Lemma trunc_contr (A : Type) `(IsTrunc A 0) : IsContr A.
Proof.
  match goal with
  | t : IsTrunc _ _ |- _ => inversion_clear t
  end. auto. Qed.

(** Contractibility is equivalent to truncation at level [-2]. *)

Lemma iff_contr_trunc (A : Type) : IsContr A <-> IsTrunc A 0.
Proof. split; [apply contr_trunc | apply trunc_contr]. Qed.

Lemma prop_trunc (A : Type) `(IsProp A) : IsTrunc A 1.
Proof.
  apply iff_trunc_succ_trunc_eq.
  intros x y. apply iff_contr_trunc.
  exists (irrel x y o irrel x x ^-1). intros a.
  rewrite a. rewrite eq_trans_sym_inv_l. reflexivity. Qed.

Lemma trunc_prop (A : Type) `(IsTrunc A 1) : IsProp A.
Proof.
  match goal with
  | t : IsTrunc _ _ |- _ => inversion_clear t
  end.
  intros x y.
  assert (a : IsContr (x = y)).
  { apply iff_contr_trunc. auto. }
  apply a. Qed.

(** Proof irrelevance is equivalent to truncation at level [-1]. *)

Lemma iff_prop_trunc (A : Type) : IsProp A <-> IsTrunc A 1.
Proof. split; [apply prop_trunc | apply trunc_prop]. Qed.

Lemma set_trunc (A : Type) `(IsSet A) : IsTrunc A 2.
Proof.
  apply iff_trunc_succ_trunc_eq.
  intros x y. apply iff_prop_trunc.
  intros a b. apply uip. Qed.

Lemma trunc_set (A : Type) `(IsTrunc A 2) : IsSet A.
Proof.
  match goal with
  | t : IsTrunc _ _ |- _ => inversion_clear t
  end.
  intros x y.
  assert (a : IsProp (x = y)).
  { apply iff_prop_trunc. auto. }
  apply a. Qed.

(** Uniqueness of identity proofs is equivalent to truncation at level [0]. *)

Lemma iff_set_trunc (A : Type) : IsSet A <-> IsTrunc A 2.
Proof. split; [apply set_trunc | apply trunc_set]. Qed.

(** Hints that construct truncations. *)

Create HintDb trunc.

#[export] Hint Resolve trunc_zero trunc_succ trunc_trunc_succ
  contr_trunc prop_trunc set_trunc : trunc.

(** Hints that eliminate truncations. *)

Create HintDb untrunc.

#[export] Hint Resolve trunc_succ_trunc_eq trunc_trunc_succ
  trunc_contr trunc_prop trunc_set : untrunc.

Lemma prop_contr_eq (A : Type) `(IsProp A) (x y : A) : IsContr (x = y).
Proof. eauto 7 with trunc untrunc. Qed.

Lemma contr_eq_prop (A : Type) `(forall x y : A, IsContr (x = y)) : IsProp A.
Proof. eauto 7 with trunc untrunc. Qed.

(** Proof irrelevance is equivalent
    to contractibility of identity proofs. *)

Lemma iff_prop_contr_eq (A : Type) :
  IsProp A <-> forall x y : A, IsContr (x = y).
Proof.
  split; [apply prop_contr_eq | apply contr_eq_prop] ||
  split; eauto 7 with trunc untrunc. Qed.

Lemma set_prop_eq (A : Type) `(IsSet A) (x y : A) : IsProp (x = y).
Proof. eauto 7 with trunc untrunc. Qed.

Lemma prop_eq_set (A : Type)
  `(forall x y : A, IsProp (x = y)) (x y : A) : IsSet A.
Proof. eauto 7 with trunc untrunc. Qed.

(** Uniqueness of identity proofs is equivalent
    to proof irrelevance of identity proofs. *)

Lemma iff_set_prop_eq (A : Type) : IsSet A <-> forall x y : A, IsProp (x = y).
Proof.
  split; [apply set_prop_eq | apply prop_eq_set] ||
  split; eauto 7 with trunc untrunc. Qed.

(** Contractibility implies proof irrelevance. *)

Lemma contr_prop (A : Type) `(IsContr A) : IsProp A.
Proof. eauto 7 with trunc untrunc. Qed.

(** Proof irrelevance implies uniqueness of identity proofs. *)

Lemma prop_set (A : Type) `(IsProp A) : IsSet A.
Proof. eauto 7 with trunc untrunc. Qed.

#[export] Hint Resolve prop_contr_eq set_prop_eq
  contr_prop prop_set : typeclass_instances.

(** True propositions are contractible. *)

Lemma prop_contr (A : Type) (x : A) `(IsProp A) : IsContr A.
Proof. exists x. apply irrel. Qed.

(** TODO Clean up. *)

From Coq Require Import
  Logic.FunctionalExtensionality Logic.PropExtensionality.
From DEZ.Is Require Import
  Extensional.
From Equations.Prop Require Import
  Logic.

(** True propositions are isomorphic to the unit type. *)

Class IsEquiv (A B : Type) (f : A -> B) : Prop := {
  is_iso_l : exists g : B -> A, IsIsoL f g;
  is_iso_r : exists g : B -> A, IsIsoR f g;
}.

Class IsEquivType (A B : Type) : Prop :=
  equiv_type : exists f : A -> B, IsEquiv f.

Lemma unit_is_equiv_type (A : Type) (x : A) `(IsProp A) : IsEquivType unit A.
Proof.
  exists (const x). split.
  - exists (const tt). intros []. reflexivity.
  - exists (const tt). intros y. unfold const. apply irrel. Qed.

Lemma is_contr_is_prop `(IsFunExtDep) (A : Type) : IsProp (IsContr A).
Proof.
  intros x y.
  assert (z : IsProp A).
  { apply contr_prop. apply x. }
  assert (w : IsSet A).
  { apply prop_set. apply z. }
  destruct x as [x a], y as [y b].
  apply eq_ex with (a y).
  assert (IsProp (forall z : A, y = z)).
  intros u v. apply fun_ext_dep. intros t. apply irrel.
  eapply irrel. Qed.

Lemma is_contr_is_contr `(IsFunExtDep) (A : Type) `(IsContr A) :
  IsContr (IsContr A).
Proof.
  apply prop_contr.
  - assumption.
  - apply is_contr_is_prop. assumption. Qed.

Lemma pi_is_prop `(IsFunExtDep) (A : Type) (P : A -> Type)
  `(forall x : A, IsProp (P x)) : IsProp (forall x : A, P x).
Proof.
  rename H0 into h.
  unfold IsProp in *.
  intros f g.
  apply fun_ext_dep.
  intros x.
  specialize (h x (f x) (g x)).
  apply h. Qed.

Lemma pi_is_contr `(IsFunExtDep) (A : Type) (P : A -> Prop)
  `(forall x : A, IsContr (P x)) : IsContr (forall x : A, P x).
Proof.
  assert (forall x : A, IsProp (P x)).
  { intros x. apply contr_prop. apply H0. }
  apply pi_is_prop in H1; try typeclasses eauto.
  apply prop_contr.
  - intros x. pose proof H0 x. destruct H2. assumption.
  - assumption. Qed.

Lemma pi_is_set `(IsPropExt) `(IsFunExtDep) (A : Type) (P : A -> Type)
  `(forall x : A, IsSet (P x)) : IsSet (forall x : A, P x).
Proof.
  rename H1 into h.
  pose proof fun (x : A) (a b : P x) =>
  set_prop_eq (h x) (x := a) (y := b) as h'.
  intros f g.
  pose proof fun x : A => h' x (f x) (g x) as k.
  pose proof pi_is_prop _ k as k'. cbv beta in k'.
  enough (IsProp (f = g)) by auto.
  pose proof (equal_f_dep (f := f) (g := g)) as l.
  pose proof (fun_ext_dep (f := f) (g := g)) as r.
  pose proof conj l r as e.
  pose proof prop_ext e as w.
  rewrite w. apply k'. Qed.

Module FromAxioms.

#[local] Instance is_prop (A : Prop) : IsProp A.
Proof.
  intros x y.
  apply proof_irrelevance. Qed.

#[export] Hint Resolve is_prop : typeclass_instances.

End FromAxioms.

Lemma trunc_pi `(IsPropExt) `(IsFunExtDep) (A : Type) (P : A -> Prop) (n : nat)
  `(forall x : A, IsTrunc (P x) n) : IsTrunc (forall x : A, P x) n.
Proof.
  revert A P H1.
  induction n as [| p t]; intros A P H1.
  - pose proof fun x : A => trunc_contr (H1 x).
    apply iff_contr_trunc.
    apply (@pi_is_contr H0 A P). apply H2.
  - apply trunc_succ.
    intros f g.
    pose proof fun (x : A) a b =>
    trunc_succ_trunc_eq (A := P x) (n := p) (H1 x) a b as u.
    pose proof fun_ext_dep (f := f) (g := g) as q.
    pose proof equal_f_dep (f := f) (g := g) as r.
    pose proof conj q r as w.
    pose proof prop_ext w.
    rewrite <- H2. apply t. intros x. apply trunc_succ_trunc_eq. apply H1. Qed.

#[local] Instance bool_is_set : IsSet bool.
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
  ~ forall (A : Type) `(IsSet A), HasEqDec A.
Proof.
  intros f.
  pose proof f (nat -> bool) as g.
  assert (x : IsSet (nat -> bool)).
  apply (pi_is_set _ _). intros _. apply (@bool_is_set).
  pose proof g x as h.
  clear f g x.
  (** Metatheoretical contradiction! *) Abort.
