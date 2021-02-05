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

Fixpoint bin_part (n : positive) : N :=
  match n with
  | xI p => 0
  | xO p => succ (bin_part p)
  | xH => 0
  end.

Arguments bin_part !_.

(** Odd part.
    Largest odd number to divide the given number.
    Sequence A000265. *)

Fixpoint odd_part (n : positive) : N :=
  match n with
  | xI p => Npos n
  | xO p => odd_part p
  | xH => Npos n
  end.

Arguments odd_part !_.

(** Binary part and odd part are related. *)

Lemma odd_part_bin_part (n : positive) :
  odd_part n * 2 ^ bin_part n = Npos n.
Proof.
  induction n as [q ei | q ei |].
  + cbn [bin_part odd_part].
    rewrite pow_0_r. rewrite mul_1_r. reflexivity.
  + cbn [bin_part odd_part].
    rewrite pow_succ_r by lia.
    rewrite mul_shuffle3.
    rewrite ei.
    reflexivity.
  + reflexivity. Qed.

Lemma odd_part_bin_part' (n : positive) :
  Npos n / 2 ^ bin_part n = odd_part n.
Proof.
  induction n as [q ei | q ei |].
  + cbn [bin_part odd_part].
    rewrite pow_0_r. rewrite div_1_r. reflexivity.
  + cbn [bin_part odd_part].
    rewrite pow_succ_r by lia.
    assert (f : 2 ^ bin_part q <> 0).
    { apply (pow_nonzero 2 (bin_part q)). lia. }
    rewrite <- div_div by lia.
    clear f.
    replace (Npos (xO q)) with (Npos q * 2) by lia.
    rewrite div_mul by lia. rewrite ei. reflexivity.
  + reflexivity. Qed.

Lemma odd_part_bin_part'' (n : positive) :
  log2 (Npos n / odd_part n) = bin_part n.
Proof.
  induction n as [q ei | q ei |].
  + cbn [bin_part odd_part].
    rewrite div_same by lia. rewrite log2_1.
    reflexivity.
  + cbn [bin_part odd_part].
    rewrite <- ei.
    replace (pos q~0) with (2 * Npos q) by lia.
    rewrite <- log2_double.
    * f_equal. admit.
    * apply div_str_pos_iff. admit. admit.
  + reflexivity. Admitted.

Module Cantor.

Definition pair_shell (n : N) : N := untri n.

Arguments pair_shell _ : assert.

Definition pair (n : N) : N * N :=
  let (u, v) := untri_rem n in
  (u - v, v).

Arguments pair _ : assert.

Definition unpair_shell (p q : N) : N := p + q.

Arguments unpair_shell _ _ : assert.

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
  rewrite tri_what. lia. Qed.

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof.
  cbv [prod_uncurry fst snd unpair unpair_shell pair].
  rewrite untri_rem_tri_untri.
  pose proof tri_untri n as l.
  pose proof tri_untri_untri_rem n as l'.
  remember (n - tri (untri n)) as p eqn : ep.
  replace (untri n - p + p) with (untri n) by lia. lia. Qed.

Theorem pair_unpair (p q : N) : pair (unpair p q) = (p, q).
Proof.
  cbv [pair unpair unpair_shell].
  rewrite untri_rem_tri_untri. f_equal.
  - rewrite tri_what. lia.
  - rewrite tri_what. lia. Qed.

Module Alternating.

Definition pair (n : N) : N * N :=
  (if even (pair_shell n) then id else prod_swap) (pair n).

Arguments pair _ : assert.

Definition unpair (p q : N) : N :=
  (if even (unpair_shell p q) then id else flip) unpair p q.

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Theorem unpair_shell_pair (n : N) :
  prod_uncurry unpair_shell (pair n) = pair_shell n.
Proof.
  cbv [prod_uncurry fst snd pair].
  destruct (even (pair_shell n)) eqn : e.
  - apply (unpair_shell_pair n).
  - cbv [unpair_shell]. rewrite add_comm.
    match goal with
    | |- context [?f
      (let (_, b) := prod_swap ?x in b)
      (let (a, _) := prod_swap ?x in a)] =>
      replace (f
        (let (_, b) := prod_swap x in b)
        (let (a, _) := prod_swap x in a))
      with (prod_uncurry f x) by (destruct x as [?a ?b]; reflexivity)
    end. apply (unpair_shell_pair n). Qed.

Theorem pair_shell_unpair (p q : N) :
  pair_shell (unpair p q) = unpair_shell p q.
Proof.
  cbv [prod_uncurry fst snd unpair].
  destruct (even (unpair_shell p q)) eqn : e.
  - apply (pair_shell_unpair p q).
  - cbv [unpair_shell]. rewrite add_comm. apply (pair_shell_unpair q p). Qed.

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof.
  cbv [prod_uncurry fst snd unpair pair].
  destruct (even (pair_shell n)) eqn : e;
  destruct (even (unpair_shell
    (let (x, _) := id (Cantor.pair n) in x)
    (let (_, y) := id (Cantor.pair n) in y))) eqn : e'.
  - apply (unpair_pair n).
  - cbv [flip Cantor.unpair]. Admitted.

Theorem pair_unpair (p q : N) : pair (unpair p q) = (p, q).
Proof.
  cbv [pair prod_uncurry fst snd].
  destruct (even (pair_shell (unpair p q))) eqn : e.
  - cbv [unpair]. destruct (even (unpair_shell p q)) eqn : e'.
    + apply (pair_unpair p q).
    + enough (true = false) by congruence. rewrite <- e, <- e'.
      rewrite <- pair_shell_unpair. reflexivity.
  - cbv [unpair]. destruct (even (unpair_shell p q)) eqn : e'.
    + enough (true = false) by congruence. rewrite <- e, <- e'.
      rewrite <- pair_shell_unpair. reflexivity.
    + cbv [prod_swap Cantor.pair flip Cantor.unpair]. Admitted.

End Alternating.

End Cantor.

Module RosenbergStrong.

Definition pair_shell (n : N) : N := sqrt n.

Arguments pair_shell _ : assert.

(** We could swap to [m - n + s] if [n <= sqrt n ^ 2 + sqrt n], but nope.
    Also [m + (s - n)], but nope. *)

Definition pair (n : N) : N * N :=
  let (s, r) := sqrtrem n in
  if s <=? r then (s - (r - s), s) else (s, r).

Arguments pair _ : assert.

Definition unpair_shell (p q : N) : N := max p q.

Arguments unpair_shell _ _ : assert.

Definition unpair (p q : N) : N :=
  if p <=? q then (q - p) + q * (1 + q) else q + p * p.

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Compute map pair_shell (seq 0 64).
Compute map (prod_uncurry unpair_shell o pair) (seq 0 64).

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
  let ((* square root *) s, (* remains *) r) := sqrtrem n in
  let (* endpoint of shell *) e := n - r in
  let (* endpoint of leg *) m := s + e in
  let (* continuation *) c :=
    if n <? m then
    (s, r) else
    (s + m - n, s) in
  (if even s then id else prod_swap) c.

Arguments pair _ : assert.

Definition unpair (p q : N) : N :=
  let ((* index in leg *) i, (* shell *) s) := min_max p q in
  let (* endpoint of shell *) e := s ^ 2 in
  let (* endpoint of leg *) m := s + e in
  let (* continuation *) c (p q : N) :=
    m - p + q in
  (if even s then id else flip) c p q.

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

Definition pair (n : N) : N * N :=
  let (s, r) := sqrtrem n in
  if s <=? r then (r - s, s) else (s, r).

Arguments pair _ : assert.

Definition unpair_shell (p q : N) : N := max p q.

Arguments unpair_shell _ _ : assert.

Definition unpair (p q : N) : N :=
  if p <=? q then p + q * (1 + q) else q + p * p.

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Compute map pair_shell (seq 0 64).
Compute map (prod_uncurry unpair_shell o pair) (seq 0 64).

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
  let ((* square root *) s, (* remains *) r) := sqrtrem n in
  let (* endpoint of shell *) e := n - r in
  let (* endpoint of leg *) m := s + e in
  let (* continuation *) c :=
    if n <? m then
    (s, r) else
    (r - s, s) in
  (if even s then id else prod_swap) c.

Arguments pair _ : assert.

Definition unpair (p q : N) : N :=
  let ((* index in leg *) i, (* shell *) s) := min_max p q in
  let (* endpoint of shell *) e := s ^ 2 in
  let (* endpoint of leg *) m := i + e in
  let (* continuation *) c (p q : N) :=
    if q <? p then
    i + e else
    s + m in
  (if even s then id else flip) c p q.

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Theorem unpair_shell_pair (n : N) :
  prod_uncurry unpair_shell (pair n) = pair_shell n.
Proof. Admitted.

Theorem pair_shell_unpair (p q : N) :
  pair_shell (unpair p q) = unpair_shell p q.
Proof. Admitted.

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (p q : N) : pair (unpair p q) = (p, q).
Proof. Admitted.

End Alternating.

End Szudzik.

Module Hyperbolic.

Lemma part_factor (n : N) (f : n <> 0) :
  exists p q : N, n = (1 + 2 * q) * 2 ^ p.
Proof.
  destruct n as [| p].
  - contradiction.
  - exists (bin_part p), ((odd_part p - 1) / 2). clear f.
    induction p as [q ei | q ei |].
    + cbn [bin_part odd_part]. rewrite pow_0_r. rewrite mul_1_r.
      rewrite <- divide_div_mul_exact. rewrite (mul_comm 2 _). rewrite div_mul.
      lia. lia. lia. cbn. replace (q~0)%positive with (2 * q)%positive by lia.
      replace (pos (2 * q)%positive) with (2 * Npos q) by lia.
      apply divide_factor_l.
    + cbn [bin_part odd_part]. rewrite pow_succ_r by lia.
      rewrite mul_assoc. lia.
    + reflexivity. Qed.

Lemma part_factor_again (p q : N) :
  exists n : N, n = (1 + 2 * q) * 2 ^ p.
Proof. exists ((1 + 2 * q) * 2 ^ p). reflexivity. Qed.

Lemma part_urgh (n : positive) :
  let p := bin_part n in
  let q := (odd_part n - 1) / 2 in
  Npos n = (1 + 2 * q) * 2 ^ p.
Proof.
  intros p' q'. subst p' q'.
  induction n as [q ei | q ei |].
  + cbn [bin_part odd_part]. rewrite pow_0_r. rewrite mul_1_r.
    rewrite <- divide_div_mul_exact. rewrite (mul_comm 2 _). rewrite div_mul.
    lia. lia. lia. cbn. replace (q~0)%positive with (2 * q)%positive by lia.
    replace (pos (2 * q)%positive) with (2 * Npos q) by lia.
    apply divide_factor_l.
  + cbn [bin_part odd_part]. rewrite pow_succ_r by lia.
    rewrite mul_assoc. lia.
  + reflexivity. Qed.

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

Definition pair (n : N) : N * N :=
  (bin_part (succ_pos n), shiftr (pred (odd_part (succ_pos n))) 1).

Arguments pair _ : assert.

Lemma pair_eqn (n : N) : pair n =
  (bin_part (succ_pos n), (odd_part (succ_pos n) - 1) / 2).
Proof. cbv [pair]. arithmetize. reflexivity. Qed.

Definition unpair_shell (p q : N) : N :=
  pos_log2 (succ_pos (shiftl q 1)) + p.

Arguments unpair_shell _ _ : assert.

Lemma unpair_shell_eqn (p q : N) : unpair_shell p q =
  pos_log2 (succ_pos (2 * q)) + p.
Proof. cbv [unpair_shell]. arithmetize. reflexivity. Qed.

Definition unpair (p q : N) : N :=
  pred (succ (shiftl q 1) * shiftl 1 p).

Arguments unpair _ _ : assert.

Lemma unpair_eqn (p q : N) : unpair p q =
  (1 + 2 * q) * 2 ^ p - 1.
Proof. cbv [unpair]. arithmetize. reflexivity. Qed.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Compute map pair_shell (seq 0 64).
Compute map (prod_uncurry unpair_shell o pair) (seq 0 64).

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof.
  cbv [prod_uncurry]. rewrite unpair_eqn. rewrite pair_eqn. cbv [fst snd].
  destruct (eqb_spec n 0) as [e | f].
  - subst n. reflexivity.
  - pose proof (part_urgh (succ_pos n)) as e. rewrite <- e.
    rewrite succ_pos_spec. lia. Qed.

Theorem pair_unpair (p q : N) : pair (unpair p q) = (p, q).
Proof.
  cbv [prod_uncurry]. rewrite pair_eqn. rewrite unpair_eqn.
  f_equal.
  - pose proof odd_part_bin_part'' (succ_pos ((1 + 2 * q) * 2 ^ p - 1)) as e'.
    admit.
  - rewrite <- odd_part_bin_part'. rewrite succ_pos_spec. arithmetize.
    replace (1 + ((1 + 2 * q) * 2 ^ p - 1))
    with ((1 + 2 * q) * 2 ^ p). 2:{ rewrite add_sub_assoc. lia.
    replace 1 with (1 * 1) by lia.
    apply mul_le_mono.
    lia.
    pose proof pow_nonzero 2 p. lia. }
    admit. Admitted.

(** TODO This is bad, but works. *)

Module Alternating.

Definition pair (n : N) : N * N :=
  let (* shell *) s := pair_shell n in
  let (* endpoint of shell *) e := pred (shiftl 1 s) in
  let (* index in shell *) i := n - e in
  if even s then pair n else pair (e + (e - i)).

Arguments pair _ : assert.

Definition unpair (p q : N) : N :=
  prod_uncurry Hyperbolic.unpair (pair (Hyperbolic.unpair p q)).

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (p q : N) : pair (unpair p q) = (p, q).
Proof. Admitted.

End Alternating.

End Hyperbolic.

(* Fixpoint steps (l : list (N * N)) : list N :=
  match l with
  | [] => []
  | (p, q) :: ((p', q') :: _) as t => if q =? q' then steps t else p :: steps t
  | (p, q) :: t => steps t
  end. *)
