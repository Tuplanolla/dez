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

Module Cantor.

Definition pair_shell (n : N) : N := untri n.

Arguments pair_shell _ : assert.

Definition pair (n : N) : N * N :=
  let (u, v) := untri_rem n in
  (u - v, v).

Arguments pair _ : assert.

Definition unpair_shell (p q : N) : N := p + q.

Arguments unpair_shell _ _ : assert.

Definition unpair (p q : N) : N :=
  q + tri (unpair_shell p q).

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

Theorem pair_shell_unpair (x : N * N) :
  pair_shell (prod_uncurry unpair x) = prod_uncurry unpair_shell x.
Proof.
  destruct x as [p q].
  cbv [prod_uncurry fst snd pair_shell unpair unpair_shell].
  rewrite tri_what. lia. Qed.

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof.
  cbv [prod_uncurry fst snd unpair unpair_shell pair].
  rewrite untri_rem_tri_untri.
  pose proof tri_untri n as l.
  pose proof tri_untri_untri_rem n as l'.
  remember (n - tri (untri n)) as p eqn : ep.
  replace (untri n - p + p) with (untri n) by lia. lia. Qed.

Theorem pair_unpair (p q : N) : pair (prod_uncurry unpair (p, q)) = (p, q).
Proof.
  cbv [pair prod_uncurry fst snd unpair unpair_shell].
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
  cbv [prod_uncurry fst snd unpair_shell pair pair_shell].
  destruct (even (untri n)) eqn : e.
  - apply (unpair_shell_pair n).
  - rewrite add_comm.
    match goal with
    | |- context [?f
      (let (_, b) := prod_swap ?x in b)
      (let (a, _) := prod_swap ?x in a)] =>
      replace (f
        (let (_, b) := prod_swap x in b)
        (let (a, _) := prod_swap x in a))
      with (prod_uncurry f x) by (destruct x; reflexivity)
    end. apply (unpair_shell_pair n). Qed.

Theorem pair_shell_unpair (x : N * N) :
  pair_shell (prod_uncurry unpair x) = prod_uncurry unpair_shell x.
Proof.
  destruct x as [p q].
  cbv [prod_uncurry fst snd pair_shell unpair unpair_shell].
  destruct (even (p + q)) eqn : e.
  - apply (pair_shell_unpair (p, q)).
  - rewrite add_comm. apply (pair_shell_unpair (q, p)). Qed.

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (p q : N) : pair (prod_uncurry unpair (p, q)) = (p, q).
Proof. Admitted.

End Alternating.

End Cantor.

Module Szudzik.

Definition pair_shell (n : N) : N := sqrt n.

Arguments pair_shell _ : assert.

Definition pair (n : N) : N * N :=
  let ((* square root *) s, (* remains *) r) := sqrtrem n in
  let (* endpoint of shell *) e := n - r in
  let (* endpoint of leg *) m := s + e in
  if n <? m then
  (s, r) else
  (r - s, s).

Arguments pair _ : assert.

Definition unpair_shell (p q : N) : N := max p q.

Arguments unpair_shell _ _ : assert.

Definition unpair (p q : N) : N :=
  let ((* index in leg *) i, (* shell *) s) := min_max p q in
  let (* endpoint of shell *) e := s ^ 2 in
  let (* endpoint of leg *) m := i + e in
  if q <? p then
  i + e else
  s + m.

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Compute map pair_shell (seq 0 64).
Compute map (prod_uncurry unpair_shell o pair) (seq 0 64).

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (p q : N) : pair (prod_uncurry unpair (p, q)) = (p, q).
Proof. Admitted.

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

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (p q : N) : pair (prod_uncurry unpair (p, q)) = (p, q).
Proof. Admitted.

End Alternating.

End Szudzik.

Module RosenbergStrong.

Definition pair_shell (n : N) : N := sqrt n.

Arguments pair_shell _ : assert.

(** We could swap to [m - n + s] if [n <= sqrt n ^ 2 + sqrt n], but nope.
    Also [m + (s - n)], but nope. *)

Definition pair (n : N) : N * N :=
  let ((* square root *) s, (* remains *) r) := sqrtrem n in
  let (* endpoint of shell *) e := n - r in
  let (* endpoint of leg *) m := s + e in
  if n <? m then
  (s, r) else
  (s + m - n, s).

Arguments pair _ : assert.

Definition unpair_shell (p q : N) : N := max p q.

Arguments unpair_shell _ _ : assert.

Definition unpair (p q : N) : N :=
  let ((* index in leg *) i, (* shell *) s) := min_max p q in
  let (* endpoint of shell *) e := s ^ 2 in
  let (* endpoint of leg *) m := s + e in
  m - p + q.

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Compute map pair_shell (seq 0 64).
Compute map (prod_uncurry unpair_shell o pair) (seq 0 64).

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (p q : N) : pair (prod_uncurry unpair (p, q)) = (p, q).
Proof. Admitted.

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

Theorem pair_unpair (p q : N) : pair (prod_uncurry unpair (p, q)) = (p, q).
Proof. Admitted.

End Alternating.

End RosenbergStrong.

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
      replace (pos (2 * q)%positive) with (2 * pos q) by lia.
      apply divide_factor_l.
    + cbn [bin_part odd_part]. rewrite pow_succ_r by lia.
      rewrite mul_assoc. lia.
    + reflexivity. Qed.

Lemma part_urgh (n : positive) :
  let p := bin_part n in
  let q := (odd_part n - 1) / 2 in
  pos n = (1 + 2 * q) * 2 ^ p.
Proof.
  intros p' q'. subst p' q'.
  induction n as [q ei | q ei |].
  + cbn [bin_part odd_part]. rewrite pow_0_r. rewrite mul_1_r.
    rewrite <- divide_div_mul_exact. rewrite (mul_comm 2 _). rewrite div_mul.
    lia. lia. lia. cbn. replace (q~0)%positive with (2 * q)%positive by lia.
    replace (pos (2 * q)%positive) with (2 * pos q) by lia.
    apply divide_factor_l.
  + cbn [bin_part odd_part]. rewrite pow_succ_r by lia.
    rewrite mul_assoc. lia.
  + reflexivity. Qed.

Definition pair_shell (n : N) : N :=
  pos_log2 (succ_pos n).

Arguments pair_shell _ : assert.

Lemma pair_shell_eqn (n : N) : pair_shell n =
  log2 (1 + n).
Proof.
  cbv [pair_shell]. induction n as [| p ei] using peano_ind.
  - reflexivity.
  - Admitted.

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

Theorem pair_unpair (p q : N) : pair (prod_uncurry unpair (p, q)) = (p, q).
Proof.
  cbv [prod_uncurry]. rewrite pair_eqn. rewrite unpair_eqn. cbv [fst snd].
  f_equal.
  - admit.
  - admit. Admitted.

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

Theorem pair_unpair (p q : N) : pair (prod_uncurry unpair (p, q)) = (p, q).
Proof. Admitted.

End Alternating.

End Hyperbolic.

(* Fixpoint steps (l : list (N * N)) : list N :=
  match l with
  | [] => []
  | (p, q) :: ((p', q') :: _) as t => if q =? q' then steps t else p :: steps t
  | (p, q) :: t => steps t
  end. *)
