(** * Contractibility and Proof Irrelevance and Uniqueness of Identity Proofs and Truncation *)

From Maniunfold.Has Require Export
  Decidability.

#[local] Open Scope type_scope.

Class IsContr (A : Type) : Prop :=
  contr : exists x : A, forall y : A, x = y.

Class IsProp (A : Type) : Prop :=
  irrel (x y : A) : x = y.

Fail Fail Class IsSet (A : Type) : Prop :=
  uip (x y : A) (a b : x = y) : a = b.

Notation IsSet := UIP.

Arguments uip {_ _ _ _} _.

(** While this type is indexed over [nat], which starts from [0],
    the truncation levels actually start from [-2]. *)

Inductive IsTrunc : nat -> Type -> Prop :=
  | trunc_zero (A : Type)
    `(IsContr A) : IsTrunc O A
  | trunc_succ (n : nat) (A : Type)
    `(forall x y : A, IsTrunc n (x = y)) : IsTrunc (S n) A.

Existing Class IsTrunc.

Lemma trunc_succ_trunc_eq (A : Type) (n : nat)
  `(IsTrunc (S n) A) (x y : A) : IsTrunc n (x = y).
Proof.
  match goal with
  | t : IsTrunc (S n) A |- _ => inversion_clear t
  end. auto. Qed.

(** Truncation at the next level is equivalent to truncation of identities. *)

Lemma trunc_succ_trunc_eq' (A : Type) (n : nat) :
  IsTrunc (S n) A <-> forall x y : A, IsTrunc n (x = y).
Proof. split; [apply trunc_succ_trunc_eq | apply trunc_succ]. Qed.

(** Truncation is cumulative. *)

Lemma trunc_trunc_succ (A : Type) (n : nat) `(IsTrunc n A) : IsTrunc (S n) A.
Proof.
  match goal with
  | t : IsTrunc n A |- _ => induction t as [A [x a] | n A t t']
  end.
  - apply trunc_succ_trunc_eq'.
    intros y z. apply trunc_zero. exists (a z o a y ^-1).
    intros c. rewrite c. rewrite eq_trans_sym_inv_l. reflexivity.
  - apply trunc_succ. auto. Qed.

Lemma contr_trunc (A : Type) `(IsContr A) : IsTrunc 0 A.
Proof. apply trunc_zero. auto. Qed.

Lemma trunc_contr (A : Type) `(IsTrunc 0 A) : IsContr A.
Proof.
  match goal with
  | t : IsTrunc 0 A |- _ => inversion_clear t
  end. auto. Qed.

(** Contractibility is equivalent to truncation at level [-2]. *)

Lemma contr_trunc' (A : Type) : IsContr A <-> IsTrunc 0 A.
Proof. split; [apply contr_trunc | apply trunc_contr]. Qed.

Lemma prop_trunc (A : Type) `(IsProp A) : IsTrunc 1 A.
Proof.
  apply trunc_succ_trunc_eq'.
  intros x y. apply contr_trunc'.
  exists (irrel x y o irrel x x ^-1). intros a.
  rewrite a. rewrite eq_trans_sym_inv_l. reflexivity. Qed.

Lemma trunc_prop (A : Type) `(IsTrunc 1 A) : IsProp A.
Proof.
  match goal with
  | t : IsTrunc 1 A |- _ => inversion_clear t
  end.
  intros x y. assert (a : IsContr (x = y)).
  { apply contr_trunc'. auto. }
  apply a. Qed.

(** Proof irrelevance is equivalent to truncation at level [-1]. *)

Lemma prop_trunc' (A : Type) : IsProp A <-> IsTrunc 1 A.
Proof. split; [apply prop_trunc | apply trunc_prop]. Qed.

Lemma set_trunc (A : Type) `(IsSet A) : IsTrunc 2 A.
Proof.
  apply trunc_succ_trunc_eq'.
  intros x y. apply prop_trunc'.
  intros a b. apply uip. Qed.

Lemma trunc_set (A : Type) `(IsTrunc 2 A) : IsSet A.
Proof.
  match goal with
  | t : IsTrunc 2 A |- _ => inversion_clear t
  end.
  intros x y. assert (a : IsProp (x = y)).
  { apply prop_trunc'. auto. }
  apply a. Qed.

(** Uniqueness of identity proofs is equivalent to truncation at level [0]. *)

Lemma set_trunc' (A : Type) : IsSet A <-> IsTrunc 2 A.
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

Lemma prop_contr_eq' (A : Type) : IsProp A <-> forall x y : A, IsContr (x = y).
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

Lemma set_prop_eq' (A : Type) : IsSet A <-> forall x y : A, IsProp (x = y).
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
