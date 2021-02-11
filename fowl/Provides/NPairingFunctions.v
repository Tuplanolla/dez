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

Fixpoint pos_partrem (n : positive) : positive * N :=
  match n with
  | xI p => (n, 0)
  | xO p => let (q, r) := pos_partrem p in (q, succ r)
  | xH => (n, 0)
  end.

Arguments pos_partrem !_.

Lemma eq_pos_partrem (n : positive) :
  let (q, r) := pos_partrem n in
  Npos q * 2 ^ r = Npos n.
Proof. Abort.

Definition partrem (n : N) : N * N :=
  match n with
  | N0 => (0, 0)
  | Npos p => let (q, r) := pos_partrem p in (Npos q, r)
  end.

Arguments partrem !_.

Lemma eq_partrem (n : N) :
  let (q, r) := partrem n in
  q * 2 ^ r = n.
Proof. Abort.

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

Module Alternating.

Definition pair (n : N) : N * N :=
  let (u, v) := untri_rem n in
  if even u then (u - v, v) else (v, u - v).
  (* if even (pair_shell n) then pair n else prod_swap (pair n). *)

Arguments pair _ : assert.

Definition unpair (p q : N) : N :=
  let s := q + p in
  if even s then q + tri s else p + tri s.
  (* if even (unpair_shell p q) then unpair p q else flip unpair p q. *)

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Theorem unpair_shell_pair (n : N) :
  prod_uncurry unpair_shell (pair n) = pair_shell n.
Proof.
  cbv [prod_uncurry fst snd pair]. (*
  destruct (even (pair_shell n)) eqn : e.
  - apply (unpair_shell_pair n).
  - cbv [unpair_shell]. rewrite add_comm.
    match goal with
    | |- context [?f
      (let (a, _) := prod_swap ?x in a)
      (let (_, b) := prod_swap ?x in b)] =>
      replace (f
        (let (a, _) := prod_swap x in a)
        (let (_, b) := prod_swap x in b))
      with (prod_uncurry (flip f) x) by (destruct x as [?a ?b]; reflexivity)
    end. apply (unpair_shell_pair n). Qed. *)
  Abort.

Theorem pair_shell_unpair (p q : N) :
  pair_shell (unpair p q) = unpair_shell p q.
Proof.
  cbv [prod_uncurry fst snd unpair]. (*
  destruct (even (unpair_shell p q)) eqn : e.
  - apply (pair_shell_unpair p q).
  - cbv [unpair_shell]. rewrite add_comm. apply (pair_shell_unpair q p). Qed. *)
  Abort.

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof.
  cbv [prod_uncurry fst snd unpair pair]. (*
  destruct (even (pair_shell n)) eqn : e;
  destruct (even (unpair_shell
    (let (x, _) := id (Cantor.pair n) in x)
    (let (_, y) := id (Cantor.pair n) in y))) eqn : e'. Admitted. *)
  Abort.

Theorem pair_unpair (p q : N) : pair (unpair p q) = (p, q).
Proof.
  cbv [pair prod_uncurry fst snd]. (*
  destruct (even (pair_shell (unpair p q))) eqn : e.
  - cbv [unpair]. destruct (even (unpair_shell p q)) eqn : e'.
    + apply (pair_unpair p q).
    + enough (true = false) by congruence. rewrite <- e, <- e'.
      rewrite <- pair_shell_unpair. reflexivity.
  - cbv [unpair]. destruct (even (unpair_shell p q)) eqn : e'.
    + enough (true = false) by congruence. rewrite <- e, <- e'.
      rewrite <- pair_shell_unpair. reflexivity.
    + cbv [prod_swap Cantor.pair flip Cantor.unpair]. Admitted. *)
  Abort.

End Alternating.

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

Module Alternating.

Definition pair (n : N) : N * N :=
  let (s, t) := sqrtrem n in
  if even s then
  if s <=? t then (s - (t - s), s) else (s, t) else
  if s <=? t then (s, s - (t - s)) else (t, s).

Arguments pair _ : assert.

Definition unpair (p q : N) : N :=
  if p <=? q then
  if even q then (q - p) + q * (1 + q) else p + q * q else
  if even p then q + p * p else (p - q) + p * (1 + p).

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (p q : N) : pair (unpair p q) = (p, q).
Proof. Admitted.

End Alternating.

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

Module Alternating.

Definition pair (n : N) : N * N :=
  let (s, t) := sqrtrem n in
  if even s then
  if s <=? t then (t - s, s) else (s, t) else
  if s <=? t then (s, t - s) else (t, s).

Arguments pair _ : assert.

Definition unpair (p q : N) : N :=
  match compare p q with
  | Eq => p * (2 + p)
  | Lt => if even q then p + q * (1 + q) else p + q * q
  | Gt => if even p then q + p * p else q + p * (1 + p)
  end.

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (p q : N) : pair (unpair p q) = (p, q).
Proof. Admitted.

End Alternating.

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

Module Alternating.

Definition pair (n : N) : N * N :=
  let (l, m) := pos_log2rem (succ_pos n) in
  if even l then pair n else pair (shiftl (n - m) 1 - m).

Arguments pair _ : assert.

#[ugly]
Lemma pair_eqn (n : N) : pair n =
  let (l, m) := log2rem (1 + n) in
  if even l then Hyperbolic.pair n else Hyperbolic.pair (2 * (n - m) - m).
Proof.
  cbv [pair]. replace (log2rem (1 + n)) with (pos_log2rem (succ_pos n)).
  - arithmetize. reflexivity.
  - induction n; try reflexivity.
    rewrite add_1_l. rewrite <- succ_pos_spec. reflexivity. Qed.

Definition unpair (p q : N) : N :=
  let (l, m) := pos_log2rem (succ_pos (shiftl q 1)) in
  let (l', m') := (p + l, m * shiftl 1 p) in
  if even l' then unpair p q else shiftl (unpair p q - m') 1 - m'.

Compute let x := 256%nat in
  Nat.eqb (length (filter id (map (fun n : N =>
  n =? (prod_uncurry unpair o pair) n) (seq 0 x)))) x.

Arguments unpair _ _ : assert.

#[ugly]
Lemma unpair_eqn (p q : N) : unpair p q =
  let (l, m) := log2rem (1 + 2 * q) in
  let (l', m') := (p + l, m * 2 ^ p) in
  if even l' then Hyperbolic.unpair p q else 2 * (Hyperbolic.unpair p q - m') - m'.
Proof.
  cbv [unpair]. replace (log2rem (1 + 2 * q)) with (pos_log2rem (succ_pos (2 * q))).
  - arithmetize. reflexivity.
  - induction q; try reflexivity. Qed.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (p q : N) : pair (unpair p q) = (p, q).
Proof. Admitted.

End Alternating.

End Hyperbolic.
