(** * Contractibility and Proof Irrelevance and Uniqueness of Identity Proofs *)

From Maniunfold Require Export
  Init.

Class IsContr (A : Type) : Prop :=
  contr : exists x : A, forall y : A, x = y.

Class IsProp (A : Type) : Prop :=
  irrel (x y : A) : x = y.

Fail Fail Class IsSet (A : Type) : Prop :=
  uip (x y : A) (a b : x = y) : a = b.

Notation IsSet := UIP.

Arguments uip {_ _ _ _} _.

Inductive IsTrunc : nat -> Type -> Prop :=
  | trunc_zero (A : Type) (x : IsContr A) : IsTrunc O A
  | trunc_trunc (n : nat) (A : Type)
    (t : forall x y : A, IsTrunc n (x = y)) : IsTrunc (S n) A.

#[local] Open Scope type_scope.

Lemma cone (A : Type) `(IsProp A) (x y z : A) (a : y = z) :
  a = irrel x z o irrel x y ^-1.
Proof. rewrite a. rewrite eq_trans_sym_inv_l. reflexivity. Qed.

Section Context.

Context (A : Type).

#[local] Open Scope type_scope.

(** Proof irrelevance is equivalent
    to contractibility of identity proofs. *)

Lemma prop_eq_contr : IsProp A <-> forall x y : A, IsContr (x = y).
Proof.
  split.
  - intros ? x y.
    assert (a := irrel x y).
    exists a. intros b.
    assert (z := x).
    rewrite (cone _ z a). rewrite (cone _ z b).
    reflexivity.
  - intros ? x y. apply (ex_proj1 contr). Qed.

End Context.

Section Context.

Context (A : Type).

#[local] Open Scope type_scope.

(** Uniqueness of identity proofs is equivalent
    to proof irrelevance of identity proofs. *)

Lemma set_eq_prop : IsSet A <-> forall x y : A, IsProp (x = y).
Proof.
  split.
  - intros ? x y a b. apply uip.
  - intros ? x y a b. apply irrel. Qed.

End Context.

Section Context.

Context (A : Type) `(IsContr A).

#[local] Open Scope type_scope.

(** Proof irrelevance is a special case of contractibility.
    In homotopy type theory parlance,
    contractible types are mere propositions. *)

#[local] Instance is_prop : IsProp A.
Proof.
  intros x y.
  destruct contr as [z e].
  rewrite <- (e x), <- (e y).
  reflexivity. Qed.

End Context.

#[export] Hint Resolve is_prop : typeclass_instances.

Section Context.

Context (A : Type) `(IsProp A).

#[local] Open Scope type_scope.

(** Uniqueness of identity proofs is a special case of proof irrelevance.
    In homotopy type theory parlance,
    mere propositions are sets. *)

#[local] Instance is_set : IsSet A.
Proof.
  assert (e : forall (x y z : A) (e : x = z), e = irrel y z o irrel y x ^-1).
  { intros x y z e. rewrite e. rewrite eq_trans_sym_inv_l. reflexivity. }
  intros x y a b. rewrite (e x x y a), (e x x y b). reflexivity. Qed.

End Context.

#[export] Hint Resolve is_set : typeclass_instances.

(** TODO Wild, but mostly useless type tricks. *)

#[local] Open Scope type_scope.

Lemma trunc_succ (A : Type) (n : nat) (t : IsTrunc n A) : IsTrunc (S n) A.
Proof.
  induction t as [A x | n A t t'].
  - pose proof x as x_. destruct x as [x' f].
    apply trunc_trunc. intros x y. apply trunc_zero.
    assert (e := f y o f x ^-1).
    hnf. exists e. intros e'.
    enough (IsSet A) by auto. typeclasses eauto.
  - apply trunc_trunc. apply t'. Qed.

Lemma trunc_prop (A : Type) `(IsProp A) : IsTrunc 1 A.
Proof.
  apply trunc_trunc. intros x y. apply trunc_zero.
  enough (IsSet A) by (exists (irrel x y); auto).
  typeclasses eauto. Qed.

Lemma trunc_set (A : Type) `(IsSet A) : IsTrunc 2 A.
Proof.
  apply trunc_trunc. intros x y.
  apply trunc_trunc.
  intros a b. apply trunc_zero.
  assert (IsProp (x = y)). intros e f. eapply uip.
  pose proof uip a b as e.
  exists e.
  intros f. eapply uip. Qed.

#[export] Hint Resolve trunc_zero trunc_prop trunc_set trunc_trunc trunc_succ : typeclass_instances.

#[local] Instance nat_is_set : IsSet nat.
Proof. apply EqDec.eqdec_uip. hnf. apply nat_eqdec. Qed.

(** Natural numbers are obviously a homotopy-5-type. *)

Goal IsTrunc 5 nat.
Proof. typeclasses eauto. Qed.
