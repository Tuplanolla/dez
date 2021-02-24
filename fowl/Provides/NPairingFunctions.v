From Coq Require Import
  Lia Lists.List NArith.NArith.
From Maniunfold.Provides Require Export
  OptionTheorems ProductTheorems NTriangularNumbers.

Import ListNotations N.

Local Open Scope N_scope.

(** Binary part.
    Largest power of two to divide the given number.
    Number of trailing zeros in the binary representation of the given number.
    Sequence A007814. *)

Fixpoint pos_bin_part (n : positive) : N :=
  match n with
  | xI p => 0
  | xO p => succ (pos_bin_part p)
  | xH => 0
  end.

Arguments pos_bin_part !_.

Definition bin_part (n : N) : N :=
  match n with
  | N0 => 0
  | Npos p => pos_bin_part p
  end.

Arguments bin_part !_.

Module Pos'.

Fixpoint odd_part (n : positive) : positive :=
  match n with
  | xI p => n
  | xO p => odd_part p
  | xH => n
  end.

Arguments odd_part !_.

End Pos'.

(** Odd part.
    Largest odd number to divide the given number.
    Sequence A000265. *)

Fixpoint pos_odd_part (n : positive) : N :=
  match n with
  | xI p => Npos n
  | xO p => pos_odd_part p
  | xH => Npos n
  end.

Arguments pos_odd_part !_.

Definition odd_part (n : N) : N :=
  match n with
  | N0 => 0
  | Npos p => pos_odd_part p
  end.

Arguments odd_part !_.

(** Binary part and odd part are related. *)

Lemma pos_odd_part_pos_bin_part (n : positive) :
  pos_odd_part n * 2 ^ pos_bin_part n = Npos n.
Proof.
  induction n as [q ei | q ei |].
  + cbn [pos_bin_part pos_odd_part].
    rewrite pow_0_r. rewrite mul_1_r. reflexivity.
  + cbn [pos_bin_part pos_odd_part].
    rewrite pow_succ_r by lia.
    rewrite mul_shuffle3.
    rewrite ei.
    reflexivity.
  + reflexivity. Qed.

(** TODO This combination of [pos_bin_part] and [pos_odd_part]. *)

Definition pos_even (n : positive) : bool :=
  match n with
  | xI p => false
  | xO p => true
  | xH => false
  end.

Arguments pos_even !_.

Definition pos_odd (n : positive) : bool := negb (pos_even n).

Arguments pos_odd !_.

Fixpoint pos_factorrem (n : positive) : N * positive :=
  match n with
  | xI p => (0, n)
  | xO p => let (q, r) := pos_factorrem p in (succ q, r)
  | xH => (0, n)
  end.

Arguments pos_factorrem !_.

Definition pos_unfactorrem (q : N) (r : positive) : positive :=
  r * Pos.shiftl 1 q.

Arguments pos_unfactorrem _ _ : assert.

Program Definition pos_factorrem_dep (n : positive) :
  {x : N * positive ! Squash (pos_odd (snd x))} :=
  Sexists _ (pos_factorrem n) _.
Next Obligation.
  intros n. apply squash.
  induction n as [p ep | p ep |]; [reflexivity | | reflexivity].
  cbn [pos_factorrem].
  destruct (pos_factorrem p) as [q r] eqn : eqr.
  apply ep. Qed.

Arguments pos_factorrem_dep _ : assert.

Definition pos_unfactorrem_dep (q : N)
  (x : {r : positive ! Squash (pos_odd r)}) : positive :=
  pos_unfactorrem q (Spr1 x).

Arguments pos_unfactorrem_dep _ !_ : assert.

Definition factorrem (n : N) : N * N :=
  match n with
  | N0 => (0, 0)
  | Npos p => let (q, r) := pos_factorrem p in (q, Npos r)
  end.

Arguments factorrem !_.

Definition unfactorrem (q r : N) : N :=
  match r with
  | N0 => 0
  | Npos p => Npos (pos_unfactorrem q p)
  end.

Arguments unfactorrem _ _ : assert.

Lemma unfactorrem_eqn (q r : N) : unfactorrem q r = r * 2 ^ q.
Proof.
  destruct r as [| s].
  - reflexivity.
  - cbv [unfactorrem pos_unfactorrem].
    rewrite <- shiftl_1_l.
    reflexivity. Qed.

Lemma unfactorrem_factorrem (n : N) :
  prod_uncurry unfactorrem (factorrem n) = n.
Proof. Admitted.

Lemma factorrem_unfactorrem' (q r : N) (x : odd r) :
  factorrem (unfactorrem q r) = (q, r).
Proof. Admitted.

Module Cantor.

Definition pair_shell (n : N) : N := untri n.

Arguments pair_shell _ : assert.

Definition unpair_shell (p q : N) : N := q + p.

Arguments unpair_shell _ _ : assert.

Definition pair (n : N) : N * N :=
  let (u, v) := untri_rem n in
  (u - v, v).

Arguments pair _ : assert.

Definition unpair (p q : N) : N := q + tri (unpair_shell p q).

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Compute map pair_shell (seq 0 64).
Compute map (prod_uncurry unpair_shell o pair) (seq 0 64).

(** Just to see if it can be done. *)

Definition pair_shell_rem (n : N) : N * N := untri_rem n.

Arguments pair_shell_rem _ : assert.

Import Program.Wf.

Definition counpair_shell (p q : N) : N := q + tri p.

Definition shell_size (i : N) : N :=
  counpair_shell (1 + i) 0 - counpair_shell i 0.

Definition shell_wf (i j : N) : Prop := j < shell_size i.

Definition shell_codom : Type :=
  {x : N * N ! Squash (prod_uncurry shell_wf x)}.

(** This shall now be a bijection proper. *)

Program Definition pair_shell' (n : N) : shell_codom :=
  Sexists _ (pair_shell_rem n) _.
Next Obligation.
  intros n. apply squash.
  cbv [prod_uncurry fst snd shell_wf pair_shell_rem shell_size counpair_shell].
  destruct (untri_rem n) as [p q] eqn : e.
  rewrite tri_succ.
  enough (q < 1 + p) by lia.
  rewrite untri_rem_tri_untri in e.
  injection e. clear e. intros eq ep. subst q p.
  pose proof tri_untri_untri_rem n as l. lia. Qed.

Theorem unpair_shell_pair (n : N) :
  prod_uncurry unpair_shell (pair n) = pair_shell n.
Proof.
  cbv [prod_uncurry fst snd unpair_shell pair pair_shell].
  rewrite untri_rem_tri_untri.
  pose proof tri_untri_untri_rem n as l.
  remember (n - tri (untri n)) as p eqn : ep.
  replace (untri n - p + p) with (untri n) by lia. lia. Qed.

Theorem pair_shell_unpair (p q : N) :
  pair_shell (unpair p q) = unpair_shell p q.
Proof.
  cbv [pair_shell unpair unpair_shell].
  replace (q + p) with (p + q) by lia.
  rewrite tri_what. lia. Qed.

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof.
  cbv [prod_uncurry fst snd unpair unpair_shell pair].
  rewrite untri_rem_tri_untri.
  pose proof tri_untri n as l.
  pose proof tri_untri_untri_rem n as l'.
  remember (n - tri (untri n)) as p eqn : ep.
  replace (p + (untri n - p)) with (untri n) by lia. lia. Qed.

Theorem pair_unpair (p q : N) : pair (unpair p q) = (p, q).
Proof.
  cbv [pair unpair unpair_shell].
  rewrite untri_rem_tri_untri. f_equal.
  - replace (q + p) with (p + q) by lia. rewrite tri_what. lia.
  - replace (q + p) with (p + q) by lia. rewrite tri_what. lia. Qed.

End Cantor.

Module RosenbergStrong.

Definition pair_shell (n : N) : N := sqrt n.

Arguments pair_shell _ : assert.

Definition unpair_shell (p q : N) : N := max q p.

Arguments unpair_shell _ _ : assert.

Definition pair (n : N) : N * N :=
  let (s, t) := sqrtrem n in
  if s <=? t then (s - (t - s), s) else (s, t).

Arguments pair _ : assert.

Definition unpair (p q : N) : N :=
  if p <=? q then (q - p) + q * (1 + q) else q + p * p.

Arguments unpair _ _ : assert.

Theorem unpair_shell_pair (n : N) :
  prod_uncurry unpair_shell (pair n) = pair_shell n.
Proof.
  cbv [prod_uncurry fst snd unpair_shell pair pair_shell].
  rewrite <- sqrtrem_sqrt. cbv [fst snd].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es.
  destruct (leb_spec s t) as [lst | lst]; lia. Qed.

Theorem pair_shell_unpair (p q : N) :
  pair_shell (unpair p q) = unpair_shell p q.
Proof.
  cbv [pair_shell unpair unpair_shell].
  rewrite <- sqrtrem_sqrt. cbv [fst snd].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es.
  destruct (leb_spec p q) as [lpq | lpq]; nia. Qed.

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof.
  cbv [prod_uncurry fst snd unpair pair].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es.
  destruct (leb_spec s t) as [lst | lst].
  - destruct (leb_spec (s - (t - s)) s) as [lst' | lst']; lia.
  - destruct (leb_spec s t) as [lst' | lst']; lia. Qed.

Theorem pair_unpair (p q : N) : pair (unpair p q) = (p, q).
Proof.
  cbv [pair unpair].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es.
  destruct (leb_spec s t) as [lst | lst].
  - destruct (leb_spec p q) as [lpq | lpq].
    + assert (e : s = q) by nia. subst s. f_equal; nia.
    + assert (f : s <> q) by nia. exfalso.
      assert (l : p <= s) by nia. nia.
  - destruct (leb_spec p q) as [lpq | lpq].
    + assert (f : s <> p) by nia. exfalso.
      assert (l : q < s) by nia. nia.
    + assert (e : s = p) by nia. subst s. f_equal; nia. Qed.

End RosenbergStrong.

Module Szudzik.

Definition pair_shell (n : N) : N := sqrt n.

Arguments pair_shell _ : assert.

Definition unpair_shell (p q : N) : N := max q p.

Arguments unpair_shell _ _ : assert.

Definition pair (n : N) : N * N :=
  let (s, t) := sqrtrem n in
  if s <=? t then (t - s, s) else (s, t).

Arguments pair _ : assert.

Definition unpair (p q : N) : N :=
  if p <=? q then p + q * (1 + q) else q + p * p.

Arguments unpair _ _ : assert.

(** Note how the three following proofs are
    nearly exactly the same as in [RosenbergStrong]. *)

Theorem unpair_shell_pair (n : N) :
  prod_uncurry unpair_shell (pair n) = pair_shell n.
Proof.
  cbv [prod_uncurry fst snd unpair_shell pair pair_shell].
  rewrite <- sqrtrem_sqrt. cbv [fst snd].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es.
  destruct (leb_spec s t) as [lst | lst]; lia. Qed.

Theorem pair_shell_unpair (p q : N) :
  pair_shell (unpair p q) = unpair_shell p q.
Proof.
  cbv [pair_shell unpair unpair_shell].
  rewrite <- sqrtrem_sqrt. cbv [fst snd].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es.
  destruct (leb_spec p q) as [lpq | lpq]; nia. Qed.

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof.
  cbv [prod_uncurry fst snd unpair pair].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es.
  destruct (leb_spec s t) as [lst | lst].
  - destruct (leb_spec (t - s) s) as [lst' | lst']; lia.
  - destruct (leb_spec s t) as [lst' | lst']; lia. Qed.

Theorem pair_unpair (p q : N) : pair (unpair p q) = (p, q).
Proof.
  cbv [pair unpair].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es.
  destruct (leb_spec s t) as [lst | lst].
  - destruct (leb_spec p q) as [lpq | lpq].
    + assert (e : s = q) by nia. subst s. f_equal; nia.
    + assert (f : s <> q) by nia. exfalso.
      assert (l : p <= s) by nia. nia.
  - destruct (leb_spec p q) as [lpq | lpq].
    + assert (f : s <> p) by nia. exfalso.
      assert (l : q < s) by nia. nia.
    + assert (e : s = p) by nia. subst s. f_equal; nia. Qed.

End Szudzik.

#[ugly]
Module Hyperbolic.

Lemma pos_bin_part_even (n : positive) :
  pos_bin_part (2 * n) = 1 + pos_bin_part n.
Proof.
  induction n as [p ei | p ei |].
  - reflexivity.
  - cbn [pos_bin_part].
    replace (1 + succ (pos_bin_part p)) with (succ (1 + pos_bin_part p)) by lia.
    rewrite <- ei. reflexivity.
  - reflexivity. Qed.

Lemma pos_bin_part_even_succ (n : positive) :
  pos_bin_part (succ_pos (2 * Npos n - 1)) = 1 + pos_bin_part n.
Proof.
  induction n as [p ei | p ei |].
  - reflexivity.
  - cbn [pos_bin_part].
    replace (1 + succ (pos_bin_part p)) with (succ (1 + pos_bin_part p)) by lia.
    rewrite <- ei. reflexivity.
  - reflexivity. Qed.

Lemma part_factor (n : N) (f : n <> 0) :
  exists p q : N, n = (1 + 2 * q) * 2 ^ p.
Proof.
  destruct n as [| p].
  - contradiction.
  - exists (pos_bin_part p), ((pos_odd_part p - 1) / 2). clear f.
    induction p as [q ei | q ei |].
    + cbn [pos_bin_part pos_odd_part]. rewrite pow_0_r. rewrite mul_1_r.
      rewrite <- divide_div_mul_exact. rewrite (mul_comm 2 _). rewrite div_mul.
      lia. lia. lia. cbn. replace (q~0)%positive with (2 * q)%positive by lia.
      replace (pos (2 * q)%positive) with (2 * Npos q) by lia.
      apply divide_factor_l.
    + cbn [pos_bin_part pos_odd_part]. rewrite pow_succ_r by lia.
      rewrite mul_assoc. lia.
    + reflexivity. Qed.

Lemma part_factor_again (p q : N) :
  exists n : N, n = (1 + 2 * q) * 2 ^ p.
Proof. exists ((1 + 2 * q) * 2 ^ p). reflexivity. Qed.

Lemma part_urgh (n : positive) :
  let p := pos_bin_part n in
  let q := (pos_odd_part n - 1) / 2 in
  Npos n = (1 + 2 * q) * 2 ^ p.
Proof.
  intros p' q'. subst p' q'.
  induction n as [q ei | q ei |].
  + cbn [pos_bin_part pos_odd_part]. rewrite pow_0_r. rewrite mul_1_r.
    rewrite <- divide_div_mul_exact. rewrite (mul_comm 2 _). rewrite div_mul.
    lia. lia. lia. cbn. replace (q~0)%positive with (2 * q)%positive by lia.
    replace (pos (2 * q)%positive) with (2 * Npos q) by lia.
    apply divide_factor_l.
  + cbn [pos_bin_part pos_odd_part]. rewrite pow_succ_r by lia.
    rewrite mul_assoc. lia.
  + reflexivity. Qed.

Lemma bin_part_odd (n : N) : bin_part (1 + 2 * n) = 0.
Proof.
  destruct n as [| p].
  - arithmetize. reflexivity.
  - induction p as [q ei | q ei |].
    + reflexivity.
    + reflexivity.
    + reflexivity. Qed.

Lemma bin_part_even (n : N) (f : n <> 0) :
  bin_part (2 * n) = 1 + bin_part n.
Proof.
  destruct n as [| p].
  - arithmetize. cbn. lia.
  - apply (pos_bin_part_even p). Qed.

Lemma bin_part_pow_2 (n p : N) (f : p <> 0) :
  bin_part (2 ^ n * p) = n + bin_part p.
Proof.
  destruct n as [| q].
  - arithmetize. reflexivity.
  - generalize dependent p. induction q as [r ei | r ei |]; intros p f.
    + replace (pos r~1) with (succ (2 * pos r)) by lia.
      rewrite pow_succ_r'.
      rewrite <- mul_assoc.
      rewrite bin_part_even.
      replace (2 * pos r) with (pos r + pos r) by lia.
      rewrite pow_add_r.
      rewrite <- mul_assoc.
      rewrite ei.
      rewrite ei. lia. lia.
      specialize (ei p).
      destruct p. lia.
      pose proof pow_nonzero 2 (pos r).
      lia.
      pose proof pow_nonzero 2 (2 * pos r).
      lia.
    + replace (pos r~0) with (2 * pos r) by lia.
      replace (2 * pos r) with (pos r + pos r) by lia.
      rewrite pow_add_r.
      rewrite <- mul_assoc.
      rewrite ei.
      rewrite ei. lia.
      lia.
      pose proof pow_nonzero 2 (pos r).
      lia.
    + arithmetize.
      destruct p. lia.
      rewrite bin_part_even.
      lia. lia. Qed.

Lemma bin_part_trivial (p q : N) :
  bin_part ((1 + 2 * q) * 2 ^ p) = p.
Proof.
  destruct p as [| r].
  - arithmetize. apply bin_part_odd.
  - generalize dependent q. induction r as [s ei | s ei |]; intros q.
    + replace (pos s~1) with (succ (2 * pos s)) by lia.
      rewrite pow_succ_r'.
      replace (2 * pos s) with (pos s + pos s) by lia.
      rewrite pow_add_r.
      rewrite mul_shuffle3.
      rewrite bin_part_even.
      rewrite mul_shuffle3.
      rewrite bin_part_pow_2.
      rewrite ei. lia.
      pose proof pow_nonzero 2 (pos s).
      lia.
      pose proof pow_nonzero 2 (pos s).
      lia.
    + replace (pos s~0) with (2 * pos s) by lia.
      replace (2 * pos s) with (pos s + pos s) by lia.
      rewrite pow_add_r.
      rewrite mul_shuffle3.
      rewrite bin_part_pow_2.
      rewrite ei. lia.
      pose proof pow_nonzero 2 (pos s).
      lia.
    + arithmetize.
      rewrite bin_part_even.
      rewrite bin_part_odd.
      lia. lia. Qed.

Lemma pos_bin_part_trivial (p q : N) :
  pos_bin_part (succ_pos ((1 + 2 * q) * 2 ^ p - 1)) = p.
Proof.
  pose proof bin_part_trivial p q as e.
  remember ((1 + 2 * q) * 2 ^ p) as r eqn : er.
  destruct r as [| s].
  - arithmetize. cbn. rewrite <- e. reflexivity.
  - replace (succ_pos (Npos s - 1)) with s. rewrite <- e. reflexivity.
    induction s.
    reflexivity.
    cbn. rewrite Pos.pred_double_spec. rewrite Pos.succ_pred; lia.
    reflexivity. Qed.

Lemma odd_part_odd (n : N) : odd_part (1 + 2 * n) = 1 + 2 * n.
Proof.
  destruct n as [| p].
  - arithmetize. reflexivity.
  - induction p as [q ei | q ei |].
    + reflexivity.
    + reflexivity.
    + reflexivity. Qed.

Lemma odd_part_even (n : N) :
  odd_part (2 * n) = odd_part n.
Proof.
  destruct n as [| p].
  - arithmetize. cbn. lia.
  - reflexivity. Qed.

Lemma odd_part_pow_2 (n p : N) (f : p <> 0) :
  odd_part (2 ^ n * p) = odd_part p.
Proof.
  destruct n as [| q].
  - arithmetize. cbn. lia.
  - generalize dependent p. induction q as [s ei | s ei |]; intros p f.
    + replace (pos s~1) with (succ (2 * pos s)) by lia.
      rewrite pow_succ_r'.
      replace (2 * pos s) with (pos s + pos s) by lia.
      rewrite pow_add_r.
      rewrite <- mul_assoc.
      rewrite odd_part_even.
      rewrite <- mul_assoc.
      rewrite ei.
      rewrite ei.
      lia.
      lia.
      pose proof pow_nonzero 2 (pos s).
      lia.
    + replace (pos s~0) with (2 * pos s) by lia.
      replace (2 * pos s) with (pos s + pos s) by lia.
      rewrite pow_add_r.
      rewrite <- mul_assoc.
      rewrite ei.
      rewrite ei.
      lia.
      lia.
      pose proof pow_nonzero 2 (pos s).
      lia.
    + arithmetize.
      rewrite odd_part_even.
      lia. Qed.

Lemma odd_part_trivial (p q : N) :
  odd_part ((1 + 2 * q) * 2 ^ p) = 1 + 2 * q.
Proof.
  destruct p as [| r].
  - arithmetize. apply odd_part_odd.
  - generalize dependent q. induction r as [s ei | s ei |]; intros q.
    + replace (pos s~1) with (succ (2 * pos s)) by lia.
      rewrite pow_succ_r'.
      replace (2 * pos s) with (pos s + pos s) by lia.
      rewrite pow_add_r.
      rewrite mul_shuffle3.
      rewrite odd_part_even.
      rewrite mul_shuffle3.
      rewrite odd_part_pow_2.
      rewrite ei. lia.
      pose proof pow_nonzero 2 (pos s).
      lia.
    + replace (pos s~0) with (2 * pos s) by lia.
      replace (2 * pos s) with (pos s + pos s) by lia.
      rewrite pow_add_r.
      rewrite mul_shuffle3.
      rewrite odd_part_pow_2.
      rewrite ei. lia.
      pose proof pow_nonzero 2 (pos s).
      lia.
    + arithmetize.
      rewrite odd_part_even.
      rewrite odd_part_odd.
      lia. Qed.

Lemma pos_odd_part_trivial (p q : N) :
  pos_odd_part (succ_pos ((1 + 2 * q) * 2 ^ p - 1)) = 1 + 2 * q.
Proof.
  pose proof odd_part_trivial p q as e.
  remember ((1 + 2 * q) * 2 ^ p) as r eqn : er.
  destruct r as [| s].
  - arithmetize. rewrite <- e. cbn. pose proof pow_nonzero 2 p. lia.
  - replace (succ_pos (Npos s - 1)) with s. rewrite <- e. reflexivity.
    induction s.
    reflexivity.
    cbn. rewrite Pos.pred_double_spec. rewrite Pos.succ_pred; lia.
    reflexivity. Qed.

Local Lemma logging (n : positive) : pos_log2 n = log2 (Npos n).
Proof.
  induction n; cbn.
  rewrite IHn; destruct n; reflexivity.
  rewrite IHn; destruct n; reflexivity.
  reflexivity. Qed.

Definition pair_shell (n : N) : N :=
  pos_log2 (succ_pos n).

Arguments pair_shell _ : assert.

Lemma pair_shell_eqn (n : N) : pair_shell n =
  log2 (1 + n).
Proof.
  cbv [pair_shell]. rewrite logging.
  rewrite succ_pos_spec. rewrite add_1_l. reflexivity. Qed.

Definition unpair_shell (p q : N) : N := p + pos_log2 (succ_pos (shiftl q 1)).

Arguments unpair_shell _ _ : assert.

Lemma unpair_shell_eqn (p q : N) : unpair_shell p q =
  p + pos_log2 (succ_pos (2 * q)).
Proof. cbv [unpair_shell]. arithmetize. reflexivity. Qed.

Definition pair (n : N) : N * N :=
  (pos_bin_part (succ_pos n), shiftr (pred (pos_odd_part (succ_pos n))) 1).

Arguments pair _ : assert.

Lemma pair_eqn (n : N) : pair n =
  (pos_bin_part (succ_pos n), (pos_odd_part (succ_pos n) - 1) / 2).
Proof. cbv [pair]. arithmetize. reflexivity. Qed.

Definition unpair (p q : N) : N := pred (succ (shiftl q 1) * shiftl 1 p).

Arguments unpair _ _ : assert.

Lemma unpair_eqn (p q : N) : unpair p q =
  (1 + 2 * q) * 2 ^ p - 1.
Proof. cbv [unpair]. arithmetize. reflexivity. Qed.

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof.
  cbv [prod_uncurry]. rewrite unpair_eqn. rewrite pair_eqn. cbv [fst snd].
  destruct (eqb_spec n 0) as [e | f].
  - subst n. reflexivity.
  - pose proof (part_urgh (succ_pos n)) as e.
    rewrite <- e. rewrite succ_pos_spec. lia. Qed.

Theorem pair_unpair (p q : N) : pair (unpair p q) = (p, q).
Proof.
  cbv [prod_uncurry]. rewrite pair_eqn. rewrite unpair_eqn.
  f_equal.
  - rewrite pos_bin_part_trivial. reflexivity.
  - rewrite pos_odd_part_trivial.
    replace (1 + 2 * q - 1) with (2 * q) by lia.
    rewrite div_Even. reflexivity. Qed.

End Hyperbolic.
