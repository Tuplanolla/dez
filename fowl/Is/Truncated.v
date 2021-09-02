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

Class IsContr (A : Type) : Prop :=
  contr : exists x : A, forall y : A, x = y.

(** ** Proof Irrelevance *)
(** ** Proposition *)

Class IsProp (A : Type) : Prop :=
  irrel (x y : A) : x = y.

(** ** Set *)
(** ** Uniqueness of Identity Proofs *)

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

Module FromAxioms.

#[local] Instance is_prop (A : Prop) : IsProp A.
Proof.
  intros x y.
  apply proof_irrelevance. Qed.

#[export] Hint Resolve is_prop : typeclass_instances.

End FromAxioms.

Lemma pi_is_set `(IsFunExtDep) (A : Type) (P : A -> Type)
  (h : forall x : A, IsSet (P x)) : IsSet (forall x : A, P x).
Proof.
  apply iff_set_prop_eq.
  intros f g.
  epose proof fun_ext_dep (f := f) (g := g) as p.
  epose proof equal_f_dep (f := f) (g := g) as q.
  epose proof fun x : A => proj1 (iff_set_prop_eq (P x)) (h x) as k.
  clear h.
  epose proof fun x : A => k x (f x) (g x) as m.
  apply pi_is_prop in m; try typeclasses eauto.
  Abort.

Lemma trunc_pi `(IsFunExtDep) (A : Type) (P : A -> Type) (n : nat)
  `(forall x : A, IsTrunc (P x) n) : IsTrunc (forall x : A, P x) n.
Proof.
  induction n as [| p t].
  - pose proof fun x : A => trunc_contr (H0 x).
    unfold IsContr in H1.
    apply iff_contr_trunc.
    hnf. Abort.

Lemma trunc_pi `(IsFunExtDep) (A : Type) (P : A -> Type) (n : nat)
  `(forall x : A, IsTrunc (P x) (S n)) : IsTrunc (forall x : A, P x) (S n).
Proof.
  induction n as [| p t].
  - apply prop_trunc.
    intros f g.
    apply fun_ext_dep.
    intros x.
    match goal with
    | t : forall x : A, IsTrunc _ _ |- _ => specialize (t x)
    end.
    apply trunc_prop in H0.
    apply irrel.
  - apply iff_trunc_succ_trunc_eq.
    intros f g. Abort.
