(** A generating function for triangular numbers and
    three variations of its inverse. *)

From Coq Require Import
  Lia Lists.List NArith.NArith.
From Maniunfold Require Import
  DatatypeTactics RewritingTactics.
From Maniunfold.Provides Require Export
  NTheorems OptionTheorems ProductTheorems.

Import N.

Local Open Scope N_scope.

(** Generating function.
    Sequence A000217. *)

Definition tri (n : N) : N :=
  shiftr (n * succ n) 1.

Arguments tri _ : assert.

Lemma tri_eqn (n : N) : tri n =
  n * (1 + n) / 2.
Proof. cbv [tri]. arithmetize. reflexivity. Qed.

(** Inverse of generating function, rounding down.
    Sequence A003056. *)

Definition untri (n : N) : N :=
  shiftr (pred (sqrt (succ (shiftl n 3)))) 1.

Arguments untri _ : assert.

Lemma untri_eqn (n : N) : untri n =
  (sqrt (1 + 8 * n) - 1) / 2.
Proof. cbv [untri]. arithmetize. reflexivity. Qed.

(** Inverse of generating function, rounding up. *)

Definition untri_up (n : N) : N :=
  match n with
  | N0 => 0
  | Npos p => succ (untri (Pos.pred_N p))
  end.

Arguments untri_up !_ : assert.

Lemma untri_up_eqn (n : N) : untri_up n =
  if n =? 0 then 0 else 1 + (sqrt (1 + 8 * (n - 1)) - 1) / 2.
Proof.
  destruct (eqb_spec n 0) as [e | f].
  - rewrite e. cbv [untri_up]. reflexivity.
  - destruct n as [| p].
    + contradiction.
    + cbv [untri_up]. rewrite pos_pred_spec. arithmetize.
      rewrite untri_eqn. reflexivity. Qed.

#[bad]
Lemma tri_subterm_Even (n : N) : Even (n * (1 + n)).
Proof.
  apply even_spec. rewrite even_mul. apply Bool.orb_true_intro.
  destruct (Even_or_Odd n) as [E | E].
  - left. apply even_spec. assumption.
  - right. rewrite add_1_l. rewrite even_succ. apply odd_spec. assumption. Qed.

#[bad]
Lemma succ_mod (n p : N) (l : 1 < n) : (succ p) mod n = succ (p mod n) mod n.
Proof.
  arithmetize.
  rewrite add_mod by lia. rewrite mod_1_l by lia. reflexivity. Qed.

#[bad]
Lemma tri_div2_mul2 (n : N) : 2 * (n * (1 + n) / 2) = n * (1 + n).
Proof.
  rewrite <- (add_0_r (2 * (_ / 2))).
  replace 0 with (n * (1 + n) mod 2).
  rewrite <- div_mod. reflexivity. lia.
  rewrite mul_add_distr_l. rewrite mul_1_r.
  rewrite add_mod by lia. rewrite mul_mod by lia.
  assert (e : n mod 2 = 0 \/ n mod 2 = 1).
  induction n as [| p eip] using peano_ind. left. reflexivity.
  destruct eip as [ei | ei].
  right. rewrite succ_mod by lia. rewrite ei. reflexivity.
  left. rewrite succ_mod by lia. rewrite ei. reflexivity.
  destruct e as [e | e].
  rewrite e. reflexivity.
  rewrite e. reflexivity. Qed.

Lemma tri_succ (n : N) : tri (succ n) = succ n + tri n.
Proof.
  cbv [tri]. arithmetize.
  rewrite (mul_add_distr_l (1 + n) 2 n).
  rewrite (div_add_l (1 + n) 2 ((1 + n) * n)).
  - rewrite (mul_comm (1 + n) n). reflexivity.
  - rewrite two_succ. apply (neq_succ_0 1). Qed.

Lemma tri_pred (n : N) : tri (pred n) = tri n - n.
Proof.
  destruct n as [| p _] using peano_ind.
  - reflexivity.
  - rewrite (pred_succ p). rewrite (tri_succ p).
    rewrite (add_comm (succ p) (tri p)). rewrite (add_sub (tri p) (succ p)).
    reflexivity. Qed.

Theorem untri_tri (n : N) : untri (tri n) = n.
Proof.
  induction n as [| p eip] using peano_ind.
  - reflexivity.
  - rewrite <- eip at 2. clear eip.
    rewrite (tri_succ p).
    cbv [tri untri]. arithmetize.
    rewrite <- (div_add_l 1 2 _) by lia.
    rewrite mul_1_l.
    rewrite add_sub_assoc.
    2:{ apply sqrt_le_square.
    match goal with
    | |- _ <= 1 + ?x => let n := fresh in set (n := x)
    end. lia. }
    rewrite (add_comm 2 _).
    rewrite <- add_sub_assoc by lia.
    replace (2 - 1) with 1 by lia.
    rewrite (add_comm _ 1).
    repeat rewrite mul_add_distr_r.
    repeat rewrite mul_add_distr_l.
    repeat rewrite mul_1_r.
    repeat rewrite mul_1_l.
    repeat rewrite add_assoc.
    replace (1 + 8) with 9 by lia.
    repeat rewrite (mul_comm _ 8).
    replace 8 with (4 * 2) by lia.
    repeat rewrite <- mul_assoc.
    replace (p + p * p) with (p * (1 + p)) by lia.
    rewrite tri_div2_mul2.
    repeat rewrite mul_add_distr_l.
    repeat rewrite mul_assoc.
    repeat rewrite add_assoc.
    replace (9 + 4 * 2 * p + 4 * p * 1 + 4 * p * p)
    with (9 + 12 * p + 4 * p * p) by lia.
    replace (1 + 4 * p * 1 + 4 * p * p) with (1 + 4 * p + 4 * p * p) by lia.
    Admitted.

Theorem untri_up_tri (n : N) : untri_up (tri n) = n.
Proof.
  destruct (tri n) as [| p] eqn : en.
  - cbv [untri_up tri] in *. arithmetize.
    apply (mul_cancel_l _ _ 2) in en; [| lia].
    rewrite (tri_div2_mul2 _) in en. lia.
  - cbv [untri_up]. rewrite pos_pred_spec. rewrite <- en.
    pose proof tri_succ (pred n) as e.
    assert (ex : tri n = succ (pred n + tri (pred n))). admit.
    rewrite ex. rewrite pred_succ. rewrite tri_pred. Admitted.

Theorem tri_untri (n : N) : tri (untri n) <= n.
Proof. Admitted.

Theorem tri_untri_up (n : N) : n <= tri (untri_up n).
Proof. Admitted.

(** Addition and multiplication are equally fast wrt both argument sizes,
    but we pretend the first one should be smaller and "more constant".
    Usually the choice is obvious,
    but here [r <= e * (2 * s - 1)] by a very slim margin
    (approaching 0 % from above). *)

(** Inverse of generating function, with a remainder.

    The remainder can be derived from [n - tri (untri n)]
    by eliminating variables via [sqrtrem_spec] and [div_eucl_spec]. *)

Definition untri_rem (n : N) : N * N :=
  let (s, r) := sqrtrem (succ (shiftl n 3)) in
  let (q, e) := div_eucl (pred s) 2 in
  (q, shiftr (r + e * pred (shiftl s 1)) 3).

Lemma untri_rem_eqn (n : N) : untri_rem n =
  let ((* square root *) s, (* remains *) r) := sqrtrem (1 + 8 * n) in
  let ((* quotient *) q, (* remainder *) e) := div_eucl (s - 1) 2 in
  (q, (r + e * (2 * s - 1)) / 8).
Proof.
  cbv [untri_rem].
  (** No hypothesis starts with [e] or [l],
      so the automatic variable names are stable. *)
  arithmetize. destruct_sqrtrem.
  arithmetize. destruct_div_eucl.
  arithmetize. reflexivity. Qed.

(** TODO This lemma helps with the next one. *)

Lemma untri_rem_eqn' (n : N) : untri_rem n =
  let (* inverse *) i := untri n in
  (i, n - tri i).
Proof.
  rewrite untri_rem_eqn. destruct_sqrtrem. destruct_div_eucl.
  rename eq0 into eq. rewrite untri_eqn. cbv zeta. rewrite tri_eqn.
  f_equal.
  - rewrite <- eq. rewrite <- es. reflexivity.
  - specialize (l1qe ltac:(lia)).
    assert (oe : e = 0 \/ e = 1) by lia.
    clear l1qe. destruct oe as [e0 | e1]; subst e; arithmetize.
    + admit.
    + admit. Abort.

Theorem untri_rem_tri (n : N) : untri_rem (tri n) = (n, 0).
Proof.
  rewrite tri_eqn. rewrite untri_rem_eqn.
  destruct_sqrtrem. destruct_div_eucl.
  specialize (l1qe ltac:(lia)).
  assert (oe : e = 0 \/ e = 1) by lia.
  clear l1qe.
  destruct oe as [e0 | e1]; subst e.
  - arithmetize. f_equal.
    + enough (2 * q = 2 * n) by lia.
      rewrite <- e0qe.
      enough (s = 1 + 2 * n) by lia.
      apply (pow_inj_l _ _ 2); [lia |].
      enough (s ^ 2 + r = (1 + 2 * n) ^ 2 + r) by lia.
      rewrite (pow_2_r s). rewrite (pow_2_r (1 + 2 * n)).
      rewrite <- e0sr.
      replace (8 * (n * (1 + n) / 2))
      with (4 * (2 * (n * (1 + n) / 2))) by lia.
      rewrite tri_div2_mul2. enough (r = 0) by lia.
      admit.
    + apply le_0_r.
      admit.
  - arithmetize. f_equal.
    + admit.
    + admit. Admitted.

Theorem tri_untri_rem (n : N) : prod_uncurry (add o tri) (untri_rem n) = n.
Proof.
  cbv [prod_uncurry compose].
  rewrite tri_eqn.
  rewrite untri_rem_eqn.
  destruct_sqrtrem.
  destruct_div_eucl.
  cbv [fst snd].
  specialize (l1qe ltac:(lia)). Admitted.

(** Inverse of generating function, partial. *)

Definition untri_error (n : N) : option N :=
  let (s, r) := sqrtrem (succ (shiftl n 3)) in
  if r =? 0 then Some (shiftr (pred s) 1) else None.

Arguments untri_error _ : assert.

Lemma untri_error_eqn (n : N) : untri_error n =
  let ((* square root *) s, (* remains *) r) := sqrtrem (1 + 8 * n) in
  if r =? 0 then Some ((s - 1) / 2) else None.
Proof.
  cbv [untri_error]. arithmetize. destruct_sqrtrem.
  arithmetize. reflexivity. Qed.

Lemma tri_untri_error_succ (n : N) :
  option_map tri (untri_error (succ n)) =
  option_map (succ o tri) (untri_error n).
Proof. Admitted.

Theorem untri_error_tri (n : N) : untri_error (tri n) = Some n.
Proof.
  cbv [untri_error tri] in *.
  destruct_sqrtrem.
  destruct (eqb_spec r 0) as [e | f].
  - subst r. clear l1sr. f_equal. arithmetize. rewrite <- es.
    rewrite <- tri_eqn. rewrite <- untri_eqn. apply untri_tri.
  - exfalso. apply f. clear f. arithmetize. Admitted.

Theorem tri_untri_error (n p : N)
  (e : option_map tri (untri_error n) = Some p) : n = p.
Proof.
  generalize dependent p.
  induction n as [| i ei] using peano_ind; intros p enp.
  - cbn in enp. injection enp. auto.
  - rewrite tri_untri_error_succ in enp. rewrite option_map_compose in enp.
    rewrite (ei (pred p)).
    + try match goal with
      | _ : context [?x =? ?y] |- _ => destruct (eqb_spec x y) as [e | f]
      end.
      cbv [option_map] in enp. destruct (untri_error i) eqn : e.
      * injection enp; clear enp; intros enp. rewrite <- enp at 2.
        arithmetize. rewrite enp. lia.
      * inversion enp.
    + cbv [tri untri_error] in *.
      destruct_sqrtrem.
      destruct (eqb_spec r 0) as [e | f].
      * cbv [option_map] in *. f_equal. arithmetize.
        assert (enp' : (1 + (s - 1) / 2 * (1 + (s - 1) / 2) / 2) = p)
        by now inversion enp.
        rewrite <- enp'.
        pose proof exist_even_odd (s - 1) as eo.
        destruct eo as [t [eo | eo]].
        -- rewrite eo.
          repeat rewrite (mul_comm 2 _). rewrite div_mul by lia.
          remember (t * (1 + t) / 2) as u eqn : eu.
          lia.
        -- rewrite eo.
          remember ((1 + 2 * t) / 2 * (1 + (1 + 2 * t) / 2) / 2) as u eqn : eu.
          lia.
      * inversion enp. Qed.
