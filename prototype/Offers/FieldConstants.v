From Maniunfold.Has Require Export
  FieldOperations FieldIdentities FieldInverses.
From Maniunfold.ShouldHave Require Export
  FieldNotations.

(** Semirings only come with zero and one out of the box,
    so we have to construct all the other natural numbers
    from repeated additions and multiplications.
    The optimal way to do this is quite complicated,
    as demonstrated in OEIS sequence A005245,
    but we can make the job more manageable
    by limiting ourselves to just addition. *)

(** The following definitions produce
    the natural numbers using the simplest suboptimal reduction tree. *)

Section Context.

Context {A : Type} {has_add : HasAdd A} {has_zero : HasZero A}
  {has_one : HasOne A}.

Fixpoint of_nat (n : nat) : A :=
  match n with
  | O => 0
  | S p => 1 + of_nat p
  end.

End Context.

(** The following definitions produce
    the natural numbers using one of the optimal reduction trees. *)

(** TODO Clean up the termination proof. *)

Require Import List Program Recdef Omega PeanoNat.

Section Context.

Import ListNotations Nat.

Context {A : Type} {has_add : HasAdd A} {has_zero : HasZero A}
  {has_one : HasOne A}.

Function of_nat' (n : nat) {measure id n} : A :=
  if n =? 0 then 0 else
  if n =? 1 then 1 else
  let p : nat := log2 n in
  if n =? 2 ^ p then of_nat' (n / 2) + of_nat' (n / 2) else
  of_nat' (n - 2 ^ p) + of_nat' (2 ^ p).
Proof.
  { intros n H0 H1 H2.
    apply eqb_neq in H0. apply eqb_neq in H1. apply eqb_eq in H2. cbv [id].
    rewrite H2.
    pose proof (neq_succ_0 1) as H.
    epose proof log2_spec n _ as H'. rewrite pow_succ_r' in H'.
    eapply le_lt_trans.
      apply div_le_mono. apply H. apply (proj1 H').
      apply (div_lt_upper_bound _ _ _ H). apply H'. }
  { intros n H0 H1 H2.
    apply eqb_neq in H0. apply eqb_neq in H1. apply eqb_neq in H2. cbv [id].
    pose proof (neq_succ_0 1) as H.
    epose proof log2_spec n _ as H'. rewrite pow_succ_r' in H'.
    rewrite le_neq. split.
      apply H'.
      apply neq_sym. apply H2. }
  { intros n H0 H1 H2.
    apply eqb_neq in H0. apply eqb_neq in H1. apply eqb_neq in H2. cbv [id].
    pose proof (neq_succ_0 1) as H.
    epose proof log2_spec n _ as H'. rewrite pow_succ_r' in H'.
    apply sub_lt.
      apply H'. epose proof mul_lt_mono_pos_l 2 0 (2 ^ log2 n) _.
      apply H3. eapply lt_trans.
      apply neq_0_lt. apply neq_sym. apply H0.
      apply H'. }
Unshelve. all: omega. Defined.

End Context.

(** The following definitions produce
    the first few natural numbers as special cases. *)

Section Context.

Context {A : Type} {has_add : HasAdd A} {has_one : HasOne A}.

Definition two : A := one + one.
Definition three : A := two + one.
Definition four : A := two + two.
Definition five : A := four + one.
Definition six : A := four + two.
Definition seven : A := four + three.
Definition eight : A := four + four.
Definition nine : A := eight + one.

End Context.
