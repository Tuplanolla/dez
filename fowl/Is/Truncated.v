(** * Contractibility and Proof Irrelevance and Uniqueness of Identity Proofs and Truncation *)

From Maniunfold Require Export
  Init.

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
  | trunc_zero (A : Type) `(IsContr A) : IsTrunc O A
  | trunc_succ (n : nat) (A : Type)
    (t : forall x y : A, IsTrunc n (x = y)) : IsTrunc (S n) A.

Existing Class IsTrunc.

Lemma zero_trunc (A : Type) `(IsTrunc O A) : IsContr A.
Proof.
  assert (t : IsTrunc 0 A) by auto.
  inversion_clear t. auto. Qed.

(** Truncation at the first level is equivalent to contractibility. *)

Lemma trunc_zero' (A : Type) : IsTrunc O A <-> IsContr A.
Proof. split; [apply zero_trunc | apply trunc_zero]. Qed.

Lemma succ_trunc (A : Type) (n : nat)
  `(IsTrunc (S n) A) (x y : A) : IsTrunc n (x = y).
Proof.
  assert (t : IsTrunc (S n) A) by auto.
  inversion_clear t. auto. Qed.

(** Truncation at the next level is equivalent to truncation of identities. *)

Lemma trunc_succ' (A : Type) (n : nat) :
  IsTrunc (S n) A <-> forall x y : A, IsTrunc n (x = y).
Proof. split; [apply succ_trunc | apply trunc_succ]. Qed.

(** Truncation is cumulative. *)

Lemma trunc_cum (A : Type) (n : nat) `(IsTrunc n A) : IsTrunc (S n) A.
Proof.
  assert (t : IsTrunc n A) by auto.
  induction t as [A [x a] | n A t t'].
  - apply trunc_succ'.
    intros y z. apply trunc_zero'. exists (a z o a y ^-1).
    intros c. rewrite c. rewrite eq_trans_sym_inv_l. reflexivity.
  - apply trunc_succ'. auto. Qed.

Lemma contr_trunc (A : Type) `(IsContr A) : IsTrunc 0 A.
Proof. apply trunc_zero'. auto. Qed.

Lemma trunc_contr (A : Type) `(IsTrunc 0 A) : IsContr A.
Proof.
  assert (t : IsTrunc 0 A) by auto.
  inversion_clear t. auto. Qed.

(** Contractibility is equivalent to truncation at level [-2]. *)

Lemma trunc_contr' (A : Type) : IsContr A <-> IsTrunc 0 A.
Proof. split; [apply contr_trunc | apply trunc_contr]. Qed.

Lemma prop_trunc (A : Type) `(IsProp A) : IsTrunc 1 A.
Proof.
  apply trunc_succ'.
  intros x y. apply trunc_contr'.
  exists (irrel x y o irrel x x ^-1). intros a.
  rewrite a. rewrite eq_trans_sym_inv_l. reflexivity. Qed.

Lemma trunc_prop (A : Type) `(IsTrunc 1 A) : IsProp A.
Proof.
  assert (t : IsTrunc 1 A) by auto.
  inversion_clear t.
  intros x y. assert (a : IsContr (x = y)).
  { apply trunc_contr'. auto. }
  apply a. Qed.

(** Proof irrelevance is equivalent to truncation at level [-1]. *)

Lemma trunc_prop' (A : Type) : IsProp A <-> IsTrunc 1 A.
Proof. split; [apply prop_trunc | apply trunc_prop]. Qed.

Lemma set_trunc (A : Type) `(IsSet A) : IsTrunc 2 A.
Proof.
  apply trunc_succ'.
  intros x y. apply trunc_prop'.
  intros a b. apply uip. Qed.

Lemma trunc_set (A : Type) `(IsTrunc 2 A) : IsSet A.
Proof.
  assert (t : IsTrunc 2 A) by auto.
  inversion_clear t.
  intros x y. assert (a : IsProp (x = y)).
  { apply trunc_prop'. auto. }
  apply a. Qed.

(** Uniqueness of identity proofs is equivalent to truncation at level [0]. *)

Lemma trunc_set' (A : Type) : IsSet A <-> IsTrunc 2 A.
Proof. split; [apply set_trunc | apply trunc_set]. Qed.

(** Hints that construct truncations. *)

Create HintDb trunc.

#[export] Hint Resolve trunc_zero trunc_succ succ_trunc trunc_cum
  contr_trunc prop_trunc set_trunc : trunc.

(** Hints that eliminate truncations. *)

Create HintDb untrunc.

#[export] Hint Resolve zero_trunc trunc_succ succ_trunc trunc_cum
  trunc_contr trunc_prop trunc_set : untrunc.

Lemma prop_contr (A : Type) `(IsProp A) (x y : A) : IsContr (x = y).
Proof. eauto with trunc untrunc. Qed.

Lemma contr_prop (A : Type) `(forall x y : A, IsContr (x = y)) : IsProp A.
Proof. eauto with trunc untrunc. Qed.

(** Proof irrelevance is equivalent
    to contractibility of identity proofs. *)

Lemma prop_contr' (A : Type) : IsProp A <-> forall x y : A, IsContr (x = y).
Proof. split; [apply prop_contr | apply contr_prop] ||
  split; eauto with trunc untrunc. Qed.

Lemma set_prop (A : Type)
  `(IsSet A) (x y : A) : IsProp (x = y).
Proof. eauto with trunc untrunc. Qed.

Lemma prop_set (A : Type)
  `(forall x y : A, IsProp (x = y)) (x y : A) : IsSet A.
Proof. eauto with trunc untrunc. Qed.

(** Uniqueness of identity proofs is equivalent
    to proof irrelevance of identity proofs. *)

Lemma set_prop' (A : Type) : IsSet A <-> forall x y : A, IsProp (x = y).
Proof. split; [apply set_prop | apply prop_set] ||
  split; eauto with trunc untrunc. Qed.

(** Contractibility implies proof irrelevance. *)

Lemma contr_prop_cum (A : Type) `(IsContr A) : IsProp A.
Proof. eauto with trunc untrunc. Qed.

(** Proof irrelevance implies uniqueness of identity proofs. *)

Lemma prop_set_cum (A : Type) `(IsProp A) : IsSet A.
Proof. eauto with trunc untrunc. Qed.

#[export] Hint Resolve contr_prop prop_set
  contr_prop_cum prop_set_cum : typeclass_instances.

#[local] Instance nat_is_set : IsSet nat.
Proof. typeclasses eauto. Qed.

(** Natural numbers are obviously a homotopy-5-type. *)

Goal IsTrunc 5 nat.
Proof. auto with trunc untrunc typeclass_instances. Qed.
