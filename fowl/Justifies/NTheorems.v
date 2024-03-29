(** * Properties of Binary Natural Numbers *)

From Coq Require Import
  NArith.NArith.
From DEZ.Has Require Export
  EquivalenceRelations Decisions OrderRelations
  Operations ArithmeticOperations.
From DEZ.Is Require Export
  TotalOrder Group Semiring.

From Coq Require Import
  Classes.DecidableClass Classes.Morphisms Lia NArith.NArith Setoids.Setoid.
From DEZ.Justifies Require Export
  PositiveTheorems.
From DEZ.Provides Require Import
  DatatypeTactics RewritingTactics.

#[local] Open Scope N_scope.

(** ** Hints Missing from the Standard Library *)

Create HintDb narith.

Definition Nsucc_eq_compat (n1 n2 : N) (a : n1 = n2) : N.succ n1 = N.succ n2.
Proof. apply N.succ_inj_wd. apply a. Qed.

#[global]
Hint Resolve
  N.succ_pred
  N.le_refl
  N.le_trans
(*   Nsucc_le_compat *)
  N.le_succ_diag_r
  N.le_le_succ_r
  N.eq_le_incl: narith.

#[global]
Hint Resolve N.le_refl N.add_comm N.add_assoc N.mul_comm N.mul_assoc N.add_0_l
  N.add_0_r N.mul_1_l
  N.mul_add_distr_r: narith.

#[global]
Hint Resolve
  (** ** Reversible simplification lemmas (no loss of information)      *)
  (** Should clearly be declared as hints                               *)

  (** Lemmas ending by eq *)
  Nsucc_eq_compat (* n = m -> N.succ n = N.succ m *)

  (** Lemmas ending by N.gt *)
(*   Nsucc_gt_compat (* m > n -> N.succ m > N.succ n *) *)
(*   Ngt_succ (* N.succ n > n *) *)
(*   Norder.Ngt_pos_0 (* N.pos p > 0 *) *)
(*   Nplus_gt_compat_l (* n > m -> p+n > p+m *) *)
(*   Nplus_gt_compat_r (* n > m -> n+p > m+p *) *)

  (** Lemmas ending by N.lt *)
(*   Pos2N.is_pos (* 0 < N.pos p *) *)
(*   N.lt_succ_diag_r (* n < N.succ n *) *)
(*   Nsucc_lt_compat (* n < m -> N.succ n < N.succ m *) *)
  N.lt_pred_l (* N.pred n < n *)
(*   Nplus_lt_compat_l (* n < m -> p+n < p+m *) *)
(*   Nplus_lt_compat_r (* n < m -> n+p < m+p *) *)

  (** Lemmas ending by N.le *)
(*   Nat2N.is_nonneg (* 0 <= N.of_nat n *) *)
(*   Pos2N.is_nonneg (* 0 <= N.pos p *) *)
  N.le_refl (* n <= n *)
  N.le_succ_diag_r (* n <= N.succ n *)
(*   Nsucc_le_compat (* m <= n -> N.succ m <= N.succ n *) *)
  N.le_pred_l (* N.pred n <= n *)
  N.le_min_l (* N.min n m <= n *)
  N.le_min_r (* N.min n m <= m *)
(*   Nplus_le_compat_l (* n <= m -> p+n <= p+m *) *)
(*   Nplus_le_compat_r (* a <= b -> a+c <= b+c *) *)
(*   N.abs_nonneg (* 0 <= |x| *) *)

  (** ** Irreversible simplification lemmas *)
  (** Probably to be declared as hints, when no other simplification is possible *)

  (** Lemmas ending by eq *)
(*   N_eq_mult (* y = 0 -> y*x = 0 *) *)
(*   Nplus_eq_compat (* n = m -> p = q -> n+p = m+q *) *)

  (** Lemmas ending by N.ge *)
(*   Norder.Nmult_ge_compat_r (* a >= b -> c >= 0 -> a*c >= b*c *) *)
(*   Norder.Nmult_ge_compat_l (* a >= b -> c >= 0 -> c*a >= c*b *) *)
(*   Norder.Nmult_ge_compat (* : *)
      a >= c -> b >= d -> c >= 0 -> d >= 0 -> a*b >= c*d *)

  (** Lemmas ending by N.lt *)
(*   Norder.Nmult_gt_0_compat (* a > 0 -> b > 0 -> a*b > 0 *) *)
  N.lt_lt_succ_r (* n < m -> n < N.succ m *)

  (** Lemmas ending by N.le *)
  N.mul_nonneg_nonneg (* 0 <= x -> 0 <= y -> 0 <= x*y *)
(*   Norder.Nmult_le_compat_r (* a <= b -> 0 <= c -> a*c <= b*c *) *)
(*   Norder.Nmult_le_compat_l (* a <= b -> 0 <= c -> c*a <= c*b *) *)
  N.add_nonneg_nonneg (* 0 <= x -> 0 <= y -> 0 <= x+y *)
  N.le_le_succ_r (* x <= y -> x <= N.succ y *)
  N.add_le_mono (* n <= m -> p <= q -> n+p <= m+q *)

  : narith.

(** These are not in [Z] either. What is going on? *)

#[local] Hint Resolve N.le_antisymm N.mul_1_r N.mul_0_r N.mul_add_distr_l : narith.

Ltac ecrush :=
  repeat (try typeclasses eauto; esplit);
  hnf in *; eauto with narith.

(** ** Decidable Total Ordering *)

#[export] Instance N_has_equiv_rel : HasEquivRel N := _=_.
#[export] Instance N_has_equiv_dec : HasEquivDec N := N.eq_dec.
#[export] Instance N_has_ord_rel : HasOrdRel N := N.le.

#[export] Instance N_le_is_refl : IsRefl N.le.
Proof. ecrush. Qed.

#[export] Instance N_le_is_trans : IsTrans N.le.
Proof. ecrush. Qed.

#[export] Instance N_le_is_connex : IsConnex N.le.
Proof.
  intros x y.
  pose proof N.le_gt_cases x y as a.
  pose proof N.lt_le_incl y x as b.
  intuition.
Qed.

#[export] Instance N_le_is_preord : IsPreord N.le.
Proof. ecrush. Qed.

#[export] Instance N_le_is_antisym : IsAntisym _=_ N.le.
Proof. ecrush. Qed.

#[export] Instance N_le_is_part_ord : IsPartOrd _=_ N.le.
Proof. ecrush. Qed.

#[export] Instance N_le_is_tot_ord : IsTotOrd _=_ N.le.
Proof. ecrush. Qed.

(** ** Additive Group *)

Module Additive.

#[export] Instance N_has_null_op : HasNullOp N := 0.
#[export] Instance N_has_bin_op : HasBinOp N := N.add.

End Additive.

#[export] Instance N_add_is_assoc : IsAssoc _=_ N.add.
Proof. ecrush. Qed.

#[export] Instance N_add_is_semigrp : IsSemigrp _=_ N.add.
Proof. ecrush. Qed.

#[local] Instance N_add_is_unl_elem_l : IsUnlElemL _=_ 0 N.add.
Proof. ecrush. Qed.

#[local] Instance N_add_is_unl_elem_r : IsUnlElemR _=_ 0 N.add.
Proof. ecrush. Qed.

#[export] Instance N_add_is_unl_elem : IsUnlElem _=_ 0 N.add.
Proof. ecrush. Qed.

#[export] Instance N_add_is_mon : IsMon _=_ 0 N.add.
Proof. ecrush. Qed.

#[export] Instance N_add_is_comm_bin_op : IsCommBinOp _=_ N.add.
Proof. ecrush. Qed.

(** ** Multiplicative Group *)

Module Multiplicative.

#[export] Instance N_has_null_op : HasNullOp N := 1.
#[export] Instance N_has_bin_op : HasBinOp N := N.mul.

End Multiplicative.

#[export] Instance N_mul_is_assoc : IsAssoc _=_ N.mul.
Proof. ecrush. Qed.

#[export] Instance N_mul_is_semigrp : IsSemigrp _=_ N.mul.
Proof. ecrush. Qed.

#[local] Instance N_mul_is_unl_elem_l : IsUnlElemL _=_ 1 N.mul.
Proof. ecrush. Qed.

#[local] Instance N_mul_is_unl_elem_r : IsUnlElemR _=_ 1 N.mul.
Proof. ecrush. Qed.

#[export] Instance N_mul_is_unl_elem : IsUnlElem _=_ 1 N.mul.
Proof. ecrush. Qed.

#[export] Instance N_mul_is_mon : IsMon _=_ 1 N.mul.
Proof. ecrush. Qed.

#[export] Instance N_mul_is_comm_bin_op : IsCommBinOp _=_ N.mul.
Proof. ecrush. Qed.

(** ** Ring *)

#[export] Instance N_has_zero : HasZero N := 0.
#[export] Instance N_has_add : HasAdd N := N.add.
#[export] Instance N_has_one : HasOne N := 1.
#[export] Instance N_has_mul : HasMul N := N.mul.

#[local] Instance N_is_distr_l : IsDistrL _=_ N.mul N.add.
Proof. ecrush. Qed.

#[local] Instance N_is_distr_r : IsDistrR _=_ N.mul N.add.
Proof. ecrush. Qed.

#[export] Instance N_is_distr : IsDistr _=_ N.mul N.add.
Proof. ecrush. Qed.

#[export] Instance N_is_semiring : IsSemiring _=_ 0 N.add 1 N.mul.
Proof. ecrush. Qed.

Module N.

(** We extend the [N] module here. *)

Export BinNat.N.

(* #[local] Open Scope positive_scope.

#[global] Instance lt_well_founded : WellFounded Pos.lt.
Proof. hnf. intros n.
  constructor. intros p.
  revert p; induction n as [q a | q a |]; intros p l.
  3:{ lia. }
  { constructor. intros r l'. apply a. clear a. assert (l'' : r < xO q) by lia. }
  { constructor. intros r l'. apply a. clear a. } Defined. *)

#[local] Open Scope N_scope.

(* #[global] Instance lt_well_founded : WellFounded lt := lt_wf_0. *)

#[global] Instance lt_well_founded : WellFounded lt.
Proof.
  intros n.
  constructor.
  induction n as [| q a] using peano_ind; intros p l.
  - lia.
  - constructor. intros r l'. apply a. clear a. lia.
Defined.

(** This incomplete set of corollaries
    would be generated by the equations plugin. *)

Corollary succ_equation_1 : succ 0 = 1.
Proof. reflexivity. Qed.

Corollary succ_equation_2 (p : positive) : succ (Npos p) = Npos (Pos.succ p).
Proof. reflexivity. Qed.

#[export] Hint Rewrite @succ_equation_1 @succ_equation_2 : succ.

Corollary pred_equation_1 : pred 0 = 0.
Proof. reflexivity. Qed.

Corollary pred_equation_2 (p : positive) : pred (Npos p) = Pos.pred_N p.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @pred_equation_1 @pred_equation_2 : pred.

(** Whether the given number is a power of two or not. *)

Equations bin (n : N) : bool :=
  bin N0 := false;
  bin (Npos p) := Pos.bin p.

(** These lemmas are missing from the standard library. *)

Lemma pos_shiftl_succ_r' (a : positive) (b : N) :
  Pos.shiftl a (succ b) = xO (Pos.shiftl a b).
Proof.
  destruct b as [| p].
  - reflexivity.
  - simp succ. unfold Pos.shiftl.
    rewrite Pos.iter_succ.
    reflexivity.
Qed.

(** These instances are missing from the standard library. *)

Global Program Instance Decidable_equiv_N (x y : N) : Decidable (x = y) := {
  Decidable_witness := eqb x y;
  Decidable_spec := _;
}.
Next Obligation. intros x y. apply eqb_eq. Qed.

Global Program Instance Decidable_le_N (x y : N) : Decidable (x <= y) := {
  Decidable_witness := leb x y;
  Decidable_spec := _;
}.
Next Obligation. intros x y. apply leb_le. Qed.

Global Program Instance Decidable_lt_N (x y : N) : Decidable (x < y) := {
  Decidable_witness := ltb x y;
  Decidable_spec := _;
}.
Next Obligation. intros x y. apply ltb_lt. Qed.

Global Instance le_add_wd : Proper (le ==> le ==> le) add.
Proof. intros n p l n' p' l'. apply add_le_mono; [lia |]. lia. Qed.

Global Instance le_mul_wd : Proper (le ==> le ==> le) mul.
Proof. intros n p l n' p' l'. apply mul_le_mono; [lia |]. lia. Qed.

Global Instance le_div2_wd : Proper (le ==> le) div2.
Proof.
  intros n p l. do 2 rewrite div2_div.
  apply div_le_mono; [lia |]. lia.
Qed.

Global Instance le_sqrt_wd : Proper (le ==> le) sqrt.
Proof. intros n p l. apply sqrt_le_mono. lia. Qed.

(** Distance between two natural numbers. *)

Definition dist (n p : N) : N :=
  max n p - min n p.

Arguments dist _ _ : assert.

Lemma dist_eqn (n p : N) : dist n p =
  if n <=? p then p - n else n - p.
Proof. cbv [dist]. destruct (leb_spec n p) as [l | l]; lia. Qed.

(** Distance is commutative. *)

Lemma dist_comm (n p : N) : dist n p = dist p n.
Proof. cbv [dist]. lia. Qed.

(** A specialization of [seq] for [N]. *)

Fixpoint seq (n : N) (p : nat) : list N :=
  match p with
  | O => nil
  | S q => n :: seq (succ n) q
  end.

(** Division, rounding down. *)

Definition pos_div (n : N) (p : positive) : N :=
  match n with
  | N0 => 0
  | Npos q => fst (pos_div_eucl q (Npos p))
  end.

Arguments pos_div !_ _.

(** Division, rounding up. *)

Definition pos_div_up (n : N) (p : positive) : N :=
  match n with
  | N0 => 0
  | Npos q =>
    match peanoView q with
    | PeanoOne => 1
    | PeanoSucc r _ => succ (fst (pos_div_eucl r (Npos p)))
    end
  end.

Arguments pos_div_up !_ _ : simpl nomatch.

(** Binary logarithm, rounding down.
    Sequence A000523. *)

Fixpoint pos_log2 (n : positive) : N :=
  match n with
  | xI p => succ (pos_log2 p)
  | xO p => succ (pos_log2 p)
  | xH => 0
  end.

Arguments pos_log2 !_.

(** Binary logarithm, rounding up.
    Sequence A029837. *)

Definition pos_log2_up (n : positive) : N :=
  match peanoView n with
  | PeanoOne => 0
  | PeanoSucc p _ => succ (pos_log2 p)
  end.

Arguments pos_log2_up _ : simpl nomatch.

(** Binary logarithm, with a remainder. *)

Fixpoint pos_log2rem (n : positive) : N * N :=
  match n with
  | xI p => let (l, m) := pos_log2rem p in (succ l, succ (double m))
  | xO p => let (l, m) := pos_log2rem p in (succ l, double m)
  | xH => (0, 0)
  end.

Arguments pos_log2rem !_.

Definition log2rem (n : N) : N * N :=
  match n with
  | N0 => (0, 0)
  | Npos p => pos_log2rem p
  end.

Arguments log2rem !_.

(** Specification for [pos_log2rem].
    Analogous in structure to [sqrtrem_spec]. *)

Lemma pos_log2rem_spec (n : positive) :
  let (l, m) := pos_log2rem n in Npos n = 2 ^ l + m /\ m < 2 ^ l.
Proof.
  induction n as [p ei | p ei |].
  - cbn. destruct (pos_log2rem p) as [q r] eqn : e. split.
    + destruct ei as [e0 e1].
      rewrite pow_succ_r by lia.
      rewrite (double_spec r).
      replace (2 * 2 ^ q + succ (2 * r))
      with (1 + 2 * (2 ^ q + r)) by lia.
      rewrite <- e0. lia.
    + destruct ei as [e0 e1].
      rewrite pow_succ_r by lia.
      rewrite (double_spec r). lia.
  - cbn. destruct (pos_log2rem p) as [q r] eqn : e. split.
    + destruct ei as [e0 e1].
      rewrite pow_succ_r by lia.
      rewrite (double_spec r).
      replace (2 * 2 ^ q + 2 * r)
      with (2 * (2 ^ q + r)) by lia.
      rewrite <- e0. lia.
    + destruct ei as [e0 e1].
      rewrite pow_succ_r by lia.
      rewrite (double_spec r).
      lia.
  - cbn. lia.
Qed.

(** Specification for [log2rem].
    Analogous in structure to [sqrtrem_spec]. *)

Lemma log2rem_spec (n : N) (l : 0 < n) :
  let (l, m) := log2rem n in n = 2 ^ l + m /\ m < 2 ^ l.
Proof.
  destruct n as [| p].
  - lia.
  - cbv [log2rem]. apply (pos_log2rem_spec p).
Qed.

(** Definition of [div] as an equation.
    Analogous in structure to [sqrtrem_sqrt]. *)

Lemma div_eucl_div (a b : N) : fst (div_eucl a b) = a / b.
Proof. reflexivity. Qed.

(** More elaborate specification for [div_eucl] than [div_eucl_spec].
    Analogous in structure to [sqrtrem_spec]. *)

Lemma div_eucl_spec' (n p : N) :
  let (q, r) := div_eucl n p in n = p * q + r /\ (p <> 0 -> r < p).
Proof.
  destruct n as [| n], p as [| p]; cbv [div_eucl] in *.
  - lia.
  - lia.
  - lia.
  - pose proof pos_div_eucl_spec n (pos p) as enp.
    pose proof pos_div_eucl_remainder n (pos p) as lnp.
    destruct (pos_div_eucl n (pos p)) as [q r]; cbv [fst snd] in *. lia.
Qed.

Ltac destruct_div_eucl' a' b' eab' ea' e0ab' l1ab' :=
  let aab' := fresh "a" a' b' in
  match goal with
  | |- context [div_eucl ?x ?y] =>
    pose proof div_eucl_spec' x y as aab';
    destruct (div_eucl x y) as [a' b'] eqn : eab';
    pose proof (eq_trans (z := a') (eq_sym (div_eucl_div x y))
      (f_equal fst eab')) as ea';
    destruct aab' as [e0ab' l1ab']
  | h : context [div_eucl ?x ?y] |- _ =>
    pose proof div_eucl_spec' x y as aab';
    destruct (div_eucl x y) as [a' b'] eqn : eab';
    pose proof (eq_trans (z := a') (eq_sym (div_eucl_div x y))
      (f_equal fst eab')) as ea';
    destruct aab' as [e0ab' l1ab']
  end.

(** Replace a call to [div_eucl] with its specification
    in the goal and hypotheses. *)

Tactic Notation "destruct_div_eucl"
  ident(a') ident(b') ident(eab') ident(ea') ident(e0ab') ident(l1ab') :=
  destruct_div_eucl' a' b' eab' ea' e0ab' l1ab'.

(** Perform [destruct_div_eucl] with fresh variable names. *)

Ltac destruct_div_eucl_fresh :=
  let a' := fresh "a" in
  let b' := fresh "b" in
  let eab' := fresh "e" a' b' in
  let ea' := fresh "e" a' in
  let e0ab' := fresh "e0" a' b' in
  let l1ab' := fresh "l1" a' b' in
  destruct_div_eucl a' b' eab' ea' e0ab' l1ab'.

Ltac destruct_sqrtrem' a' b' eab' ea' e0ab' l1ab' :=
  let aab' := fresh "a" a' b' in
  match goal with
  | |- context [sqrtrem ?x] =>
    pose proof sqrtrem_spec x as aab';
    destruct (sqrtrem x) as [a' b'] eqn : eab';
    pose proof (eq_trans (z := a') (eq_sym (sqrtrem_sqrt x))
      (f_equal fst eab')) as ea';
    destruct aab' as [e0ab' l1ab']
  | h : context [sqrtrem ?x] |- _ =>
    pose proof sqrtrem_spec x as aab';
    destruct (sqrtrem x) as [a' b'] eqn : eab';
    pose proof (eq_trans (z := a') (eq_sym (sqrtrem_sqrt x))
      (f_equal fst eab')) as ea';
    destruct aab' as [e0ab' l1ab']
  end.

(** Replace a call to [sqrtrem] with its specification
    in the goal and hypotheses. *)

Tactic Notation "destruct_sqrtrem"
  ident(a') ident(b') ident(eab') ident(ea') ident(e0ab') ident(l1ab') :=
  destruct_sqrtrem' a' b' eab' ea' e0ab' l1ab'.

(** Perform [destruct_sqrtrem] with fresh variable names. *)

Ltac destruct_sqrtrem_fresh :=
  let a' := fresh "a" in
  let b' := fresh "b" in
  let eab' := fresh "e" a' b' in
  let ea' := fresh "e" a' in
  let e0ab' := fresh "e0" a' b' in
  let l1ab' := fresh "l1" a' b' in
  destruct_sqrtrem a' b' eab' ea' e0ab' l1ab'.

(** Minimum with a remainder.
    Analogous in structure to [div_eucl] and [sqrtrem]. *)

Definition min_max (n p : N) : N * N :=
  if n <? p then (n, p) else (p, n).

Arguments min_max _ _ : assert.

(** Specification for [min_max].
    Analogous in structure to [min_spec] and [max_spec]. *)

Lemma min_max_spec (n p : N) :
  n < p /\ min_max n p = (n, p) \/
  p <= n /\ min_max n p = (p, n).
Proof. cbv [min_max]. destruct (ltb_spec n p); auto. Qed.

(** Definition of [min] as an equation.
    Analogous in structure to [sqrtrem_sqrt]. *)

Lemma min_max_min (a b : N) : fst (min_max a b) = min a b.
Proof.
  destruct (min_max_spec a b) as [[l e] | [l e]],
  (min_spec a b) as [[l' e'] | [l' e']].
  - rewrite e, e'. auto.
  - rewrite e, e'. lia.
  - rewrite e, e'. lia.
  - rewrite e, e'. auto.
Qed.

(** Definition of [max] as an equation.
    Analogous in structure to [sqrtrem_sqrt]. *)

Lemma min_max_max (a b : N) : snd (min_max a b) = max a b.
Proof.
  destruct (min_max_spec a b) as [[l e] | [l e]],
  (max_spec a b) as [[l' e'] | [l' e']].
  - rewrite e, e'. auto.
  - rewrite e, e'. lia.
  - rewrite e, e'. lia.
  - rewrite e, e'. auto.
Qed.

Ltac destruct_min_max' a' b' eab' ea' eb' l0ab' e1ab' :=
  let aab' := fresh "a" a' b' in
  match goal with
  | |- context [min_max ?x ?y] =>
    pose proof min_max_spec x y as aab';
    destruct (min_max x y) as [a' b'] eqn : eab';
    pose proof (eq_trans (z := a') (eq_sym (min_max_min x y))
      (f_equal fst eab')) as ea';
    pose proof (eq_trans (z := b') (eq_sym (min_max_max x y))
      (f_equal snd eab')) as eb';
    destruct aab' as [[l0ab' e1ab'] | [l0ab' e1ab']]
  | h : context [min_max ?x ?y] |- _ =>
    pose proof min_max_spec x y as aab';
    destruct (min_max x y) as [a' b'] eqn : eab';
    pose proof (eq_trans (z := a') (eq_sym (min_max_min x y))
      (f_equal fst eab')) as ea';
    pose proof (eq_trans (z := b') (eq_sym (min_max_max x y))
      (f_equal snd eab')) as eb';
    destruct aab' as [[l0ab' e1ab'] | [l0ab' e1ab']]
  end.

(** Replace a call to [min_max] with its specification
    in the goal and hypotheses. *)

Tactic Notation "destruct_min_max"
  ident(a') ident(b') ident(eab') ident(ea') ident(eb') ident(l0ab') ident(e1ab') :=
  destruct_min_max' a' b' eab' ea' eb' l0ab' e1ab'.

(** Perform [destruct_min_max] with fresh variable names. *)

Ltac destruct_min_max_fresh :=
  let a' := fresh "a" in
  let b' := fresh "b" in
  let eab' := fresh "e" a' b' in
  let ea' := fresh "e" a' in
  let eb' := fresh "e" b' in
  let l0ab' := fresh "l0" a' b' in
  let e1ab' := fresh "e1" a' b' in
  destruct_min_max a' b' eab' ea' eb' l0ab' e1ab'.

(** These lemmas are missing from the standard library. *)

Lemma shiftl_1_r (a : N) : shiftl a 1 = a * 2.
Proof. rewrite shiftl_mul_pow2. rewrite pow_1_r. reflexivity. Qed.

Lemma shiftr_1_l (n : N) : shiftr 1 n = 1 / 2 ^ n.
Proof. rewrite shiftr_div_pow2. reflexivity. Qed.

Lemma shiftr_1_r (a : N) : shiftr a 1 = a / 2.
Proof. rewrite <- div2_spec. rewrite div2_div. reflexivity. Qed.

(** If we admit that subtraction is saturative (by [sub_0_l]),
    we might as well admit that division and binary logarithm are total
    (by [div_0_r] and [log2_0] respectively). *)

Lemma div_0_r (a : N) : a / 0 = 0.
Proof. destruct a as [| p]; reflexivity. Qed.

Lemma log2_0 : log2 0 = 0.
Proof. reflexivity. Qed.

(** Eliminate all occurrences of
    [shiftl], [double], [succ], [shiftr], [div2] and [pred]. *)

Ltac eliminate :=
  (** Eliminate [shiftl 0 _].
      This shortcut is equivalent to [shiftl_mul_pow2]
      followed by [mul_0_l]. *)
  repeat rewrite shiftl_0_l in *;
  (** Eliminate [shiftl _ 0].
      This shortcut is equivalent to [shiftl_mul_pow2]
      followed by [pow_0_r] and [mul_1_r]. *)
  repeat rewrite shiftl_0_r in *;
  (** Eliminate [shiftl 1 _] into [2 ^ _].
      This shortcut is equivalent to [shiftl_mul_pow2]
      followed by [mul_1_l]. *)
  repeat rewrite shiftl_1_l in *;
  (** Eliminate [shiftl _ 1] into [_ * 2].
      This shortcut is equivalent to [shiftl_mul_pow2]
      followed by [pow_1_r]. *)
  repeat rewrite shiftl_1_r in *;
  (** Eliminate [shiftl _ _] into [_ * 2 ^ _]. *)
  repeat rewrite shiftl_mul_pow2 in *;
  (** Eliminate [double _] into [2 * _]. *)
  repeat rewrite double_spec in *;
  (** Eliminate [succ _] into [1 + _]. *)
  repeat rewrite <- add_1_l in *;
  (** Eliminate [shiftr 0 _].
      This shortcut is equivalent to [shiftr_div_pow2]
      followed by [div_0_l] with [pow_nonzero]. *)
  repeat rewrite shiftr_0_l in *;
  (** Eliminate [shiftr _ 0].
      This shortcut is equivalent to [shiftr_div_pow2]
      followed by [pow_0_r] and [div_1_r]. *)
  repeat rewrite shiftr_0_r in *;
  (** Eliminate [shiftr 1 _] into [1 / 2 ^ _].
      This shortcut is equivalent to [shiftr_div_pow2]. *)
  repeat rewrite shiftr_1_l in *;
  (** Eliminate [shiftr _ 1] into [_ / 2].
      This shortcut is equivalent to [shiftr_div_pow2]
      followed by [pow_1_r]. *)
  repeat rewrite shiftr_1_r in *;
  (** Eliminate [shiftr _ _] into [_ / 2 ^ _]. *)
  repeat rewrite shiftr_div_pow2 in *;
  (** Eliminate [div2 _] into [_ / 2]. *)
  repeat rewrite div2_div in *;
  (** Eliminate [pred] into [_ - 1]. *)
  repeat rewrite <- sub_1_r in *;
  idtac.

(** Simplify occurrences of
    [_ ^ _], [_ * _], [_ + _], [log2], [_ / _] and [_ - _].
    Rewrite rules that produce subgoals will fail,
    unless they can be immediately proven with [force]. *)

Ltac simplify_by force :=
  (** Reduce [_ ^ _], [_ * _], [_ + _], [log2], [_ / _] and [_ - _]. *)
  (** Try to eliminate [0 ^ _]. *)
  repeat rewrite pow_0_l in * by force;
  (** Eliminate [_ ^ 0]. *)
  repeat rewrite pow_0_r in *;
  (** Eliminate [1 ^ _]. *)
  repeat rewrite pow_1_l in *;
  (** Eliminate [_ ^ 1]. *)
  repeat rewrite pow_1_r in *;
  (** Do not try to eliminate [_ ^ _],
      because it would be impossible. *)
  (* repeat rewrite _ in *; *)
  (** Eliminate [0 * _]. *)
  repeat rewrite mul_0_l in *;
  (** Eliminate [_ * 0]. *)
  repeat rewrite mul_0_r in *;
  (** Eliminate [1 * _]. *)
  repeat rewrite mul_1_l in *;
  (** Eliminate [_ * 1]. *)
  repeat rewrite mul_1_r in *;
  (** Do not try to eliminate [_ * _],
      because it would be impossible. *)
  (* repeat rewrite _ in *; *)
  (** Eliminate [0 + _]. *)
  repeat rewrite add_0_l in *;
  (** Eliminate [_ + 0]. *)
  repeat rewrite add_0_r in *;
  (** Do not try to eliminate [_ + _],
      because it would be impossible. *)
  (* repeat rewrite _ in *; *)
  (** Eliminate [log2 0].
      This is specific to the way [log2] is defined. *)
  repeat rewrite log2_0 in *;
  (** Eliminate [log2 1]. *)
  repeat rewrite log2_1 in *;
  (** Eliminate [log2 2]. *)
  repeat rewrite log2_2 in *;
  (** Do not eliminate [log2 _],
      because it would be impossible. *)
  (* repeat rewrite _ in *; *)
  (** Try to eliminate [0 / _]. *)
  repeat rewrite div_0_l in * by force;
  (** Eliminate [_ / 0].
      This is specific to the way [div] is defined. *)
  repeat rewrite div_0_r in *;
  (** Try to eliminate [1 / _]. *)
  repeat rewrite div_1_l in * by force;
  (** Eliminate [_ / 1]. *)
  repeat rewrite div_1_r in *;
  (** Do not try to eliminate [_ / _],
      because it would be impossible. *)
  (* repeat rewrite _ in *; *)
  (** Eliminate [0 - _].
      This is specific to the way [sub] is defined. *)
  repeat rewrite sub_0_l in *;
  (** Eliminate [_ - 0]. *)
  repeat rewrite sub_0_r in *;
  (** Do not try to eliminate [_ - _],
      because it would be impossible. *)
  (* repeat rewrite _ in *; *)
  idtac.

(** Prepare for reduction or reduce occurrences of
    [_ ^ _], [_ * _], [_ + _], [log2], [_ / _] and [_ - _].
    Rewrite rules that produce subgoals will fail,
    unless they can be immediately proven with [force]. *)

Ltac preduce :=
  (** Reduce [_ ^ _], [_ * _], [_ + _], [log2], [_ / _] and [_ - _]. *)
  repeat reduce_2 is_N is_N pow;
  repeat reduce_2 is_N is_N mul;
  repeat reduce_2 is_N is_N add;
  repeat reduce_1 is_N log2;
  repeat reduce_2 is_N is_N div;
  repeat reduce_2 is_N is_N sub;
  (** Commute [_ * _] and [_ + _],
      so that constants always appear on the left side
      (corresponding to the structurally recursive parameter). *)
  repeat recomm_2_0 is_N mul mul_comm;
  repeat recomm_2_0 is_N add add_comm;
  (** Associate [_ * _] and [_ + _],
      so that constants always appear on the deeper level
      (and thus reduce). *)
  repeat reassoc_2 is_N mul mul_assoc;
  repeat reassoc_2 is_N add add_assoc;
  idtac.

(** Convert expressions involving bit manipulation
    into expressions involving basic arithmetic.

    The conversion repeats three steps
    until they no longer make progress in the proof.
    In the first step, we eliminate occurrences of
    [shiftl], [double], [succ], [shiftr], [div2] and [pred], and
    in the remaining steps, we simplify and reduce occurrences of
    [_ ^ _], [_ * _], [_ + _], [log2], [_ / _] and [_ - _].

    After the conversion,
    we expect two kinds of properties to hold.
    Most importantly,
    no occurrence of [_ * _] or [_ + _]
    will have constants appear on the right side,
    no occurrence of [_ ^ _], [_ / _] or [_ - _]
    will have constants appear on both sides and
    no occurrence of [log2] will have constants appear anywhere.
    Less importantly,
    no occurrence of [0], [1] or [2] should be unnecessary
    according to the algebraic structure of the operations. *)

Ltac arithmetize_by force := eliminate; repeat (simplify_by force; preduce).

(** Specialization of [arithmetize_by] using [lia]. *)

Ltac arithmetize := arithmetize_by lia.

(** Dividing an even number by two. *)

Lemma div_Even (n : N) : 2 * n / 2 = n.
Proof.
  induction n as [| p ei] using peano_ind; arithmetize.
  - reflexivity.
  - replace (2 * (1 + p)) with (1 * 2 + 2 * p) by lia.
    rewrite div_add_l by lia. rewrite ei. lia.
Qed.

(** Dividing an odd number by two. *)

Lemma div_Odd (n : N) : (1 + 2 * n) / 2 = n.
Proof.
  induction n as [| p ei] using peano_ind; arithmetize.
  - reflexivity.
  - replace (1 + 2 * (1 + p)) with (1 * 2 + (1 + 2 * p)) by lia.
    rewrite div_add_l by lia. rewrite ei. lia.
Qed.

(** Sum of two consecutive natural numbers is odd. *)

Lemma Odd_add_consecutive (n : N) : Odd (n + (1 + n)).
Proof.
  induction n as [| p xi] using peano_ind; arithmetize.
  - exists 0. reflexivity.
  - destruct xi as [q e]. exists (1 + q). lia.
Qed.

(** Product of two consecutive natural numbers is even. *)

Lemma Even_mul_consecutive (n : N) : Even (n * (1 + n)).
Proof.
  destruct (Even_or_Odd n) as [x | x].
  - destruct x as [p e]. exists (p * (1 + 2 * p)). lia.
  - destruct x as [p e]. exists ((2 * p + 1) * (1 + p)). lia.
Qed.

End N.
