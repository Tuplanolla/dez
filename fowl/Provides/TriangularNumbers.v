(** * Triangular numbers and their properties over [N]. *)

From Coq Require Import
  Lia Lists.List NArith.NArith.
From Maniunfold Require Import
  DatatypeTactics RewritingTactics.
From Maniunfold.Provides Require Export
  NTheorems OptionTheorems ProductTheorems.

Import N.

Local Open Scope N_scope.

Local Lemma again_l (n p : N) : (1 + (1 + 2 * n)) * p = 2 * (1 + n) * p.
Proof. lia. Qed.

Local Lemma again_r (n p : N) : n * (1 + (1 + 2 * p)) = 2 * n * (1 + p).
Proof. lia. Qed.

(** A generating function.
    Sequence A000217. *)

Definition tri (n : N) : N :=
  shiftr (n * succ n) 1.

Arguments tri _ : assert.

Lemma tri_eqn (n : N) : tri n =
  n * (1 + n) / 2.
Proof. cbv [tri]. arithmetize. reflexivity. Qed.

(** A weak inverse of the generating function, rounding down.
    Sequence A003056. *)

Definition untri (n : N) : N :=
  shiftr (pred (sqrt (succ (shiftl n 3)))) 1.

Arguments untri _ : assert.

Lemma untri_eqn (n : N) : untri n =
  (sqrt (1 + 8 * n) - 1) / 2.
Proof. cbv [untri]. arithmetize. reflexivity. Qed.

(** A weak inverse of the generating function, rounding up. *)

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
    + lia.
    + cbv [untri_up]. rewrite pos_pred_spec. arithmetize.
      rewrite untri_eqn. reflexivity. Qed.

(** The generating function is injective. *)

Lemma tri_inj (n p : N) (e : tri n = tri p) : n = p.
Proof.
  do 2 rewrite tri_eqn in e.
  destruct (exist_even_odd n) as [q [eq | eq]],
  (exist_even_odd p) as [r [er | er]].
  - rewrite eq, er in e.
    do 2 rewrite <- (mul_assoc 2) in e. do 2 rewrite div_even in e. nia.
  - rewrite eq, er in e. rewrite again_r in e.
    do 2 rewrite <- (mul_assoc 2) in e. do 2 rewrite div_even in e. nia.
  - rewrite eq, er in e. rewrite again_r in e.
    do 2 rewrite <- (mul_assoc 2) in e. do 2 rewrite div_even in e. nia.
  - rewrite eq, er in e. do 2 rewrite again_r in e.
    do 2 rewrite <- (mul_assoc 2) in e. do 2 rewrite div_even in e. nia. Qed.

(** The generating function is not surjective. *)

Lemma tri_nsurj : exists n : N, forall p : N, n <> tri p.
Proof.
  exists 2. intros p. induction p as [| q _] using peano_ind; arithmetize.
  - intros e. inversion e.
  - rewrite tri_eqn. destruct (exist_even_odd q) as [r [er | er]].
    + rewrite er. rewrite again_r.
      rewrite <- (mul_assoc 2). rewrite div_even. lia.
    + rewrite er. rewrite again_l.
      rewrite <- (mul_assoc 2). rewrite div_even. lia. Qed.

(** The generating function preserves zeroness. *)

Lemma tri_eq_0 (n : N) (e : tri n = 0) : n = 0.
Proof. apply tri_inj. apply e. Qed.

(** The generating function preserves nonzeroness. *)

Lemma tri_neq_0 (n : N) (f : tri n <> 0) : n <> 0.
Proof. intros e. apply f. rewrite e. reflexivity. Qed.

(** The function [untri] is an inverse of [tri]. *)

Theorem untri_tri (n : N) : untri (tri n) = n.
Proof.
  rewrite untri_eqn, tri_eqn.
  replace (8 * (n * (1 + n) / 2)) with (4 * (2 * (n * (1 + n) / 2))) by lia.
  rewrite <- divide_div_mul_exact; [| lia |].
  - rewrite div_even.
    replace (1 + 4 * (n * (1 + n))) with ((1 + 2 * n) * (1 + 2 * n)) by lia.
    rewrite sqrt_square.
    replace (1 + 2 * n - 1) with (2 * n) by lia.
    rewrite div_even. reflexivity.
  - apply mod_divide; [lia |]. apply mod_mul_consecutive. Qed.

(** The function [untri_up] is an inverse of [tri]. *)

Theorem untri_up_tri (n : N) : untri_up (tri n) = n.
Proof.
  rewrite untri_up_eqn.
  destruct (eqb_spec (tri n) 0) as [e | f].
  - symmetry. apply tri_eq_0. apply e.
  - apply tri_neq_0 in f. rewrite tri_eqn.
    replace (8 * (n * (1 + n) / 2 - 1))
    with (4 * (2 * (n * (1 + n) / 2) - 2)) by lia.
    rewrite <- divide_div_mul_exact; [| lia |].
    + rewrite div_even.
      remember (1 + 4 * (n * (1 + n) - 2)) as p eqn : ep.
      destruct (exist_even_odd (sqrt p - 1)) as [q [eq | eq]].
      * rewrite eq. rewrite div_even.
        destruct (sqrt_spec' p) as [l0 l1]. nia.
      * rewrite eq. rewrite div_odd.
        destruct (sqrt_spec' p) as [l0 l1]. nia.
    + apply mod_divide; [lia |]. apply mod_mul_consecutive. Qed.

(** The function [tri] provides a lower bound for inverses of [untri]. *)

Lemma tri_untri (n : N) : tri (untri n) <= n.
Proof.
  rewrite untri_eqn, tri_eqn.
  remember (1 + 8 * n) as p eqn : ep.
  destruct (exist_even_odd (sqrt p - 1)) as [q [eq | eq]].
  - rewrite eq. rewrite div_even.
    destruct (exist_even_odd q) as [r [er | er]].
    + rewrite er. rewrite <- (mul_assoc 2).
      rewrite div_even. destruct (sqrt_spec' p) as [l0 l1]. nia.
    + rewrite er. rewrite again_r. rewrite <- (mul_assoc 2).
      rewrite div_even. destruct (sqrt_spec' p) as [l0 l1]. nia.
  - rewrite eq. rewrite div_odd.
    destruct (exist_even_odd q) as [r [er | er]].
    + rewrite er. rewrite <- (mul_assoc 2).
      rewrite div_even. destruct (sqrt_spec' p) as [l0 l1]. nia.
    + rewrite er. rewrite again_r. rewrite <- (mul_assoc 2).
      rewrite div_even. destruct (sqrt_spec' p) as [l0 l1]. nia. Qed.

(** The function [tri] provides an upper bound for inverses of [untri]. *)

Lemma tri_untri_up (n : N) : n <= tri (untri_up n).
Proof.
  rewrite untri_up_eqn, tri_eqn.
  destruct (eqb_spec n 0) as [e | f].
  - arithmetize. lia.
  - remember (1 + 8 * (n - 1)) as p eqn : ep.
    rewrite <- div_add_l by lia.
    assert (fp : sqrt p <> 0).
    { destruct (sqrt_spec' p) as [l0 l1]. nia. }
    replace (1 * 2 + (sqrt p - 1)) with (1 + sqrt p) by lia.
    destruct (exist_even_odd (1 + sqrt p)) as [q [eq | eq]].
    + rewrite eq. rewrite div_even.
      destruct (exist_even_odd q) as [r [er | er]].
      * rewrite er. rewrite <- (mul_assoc 2).
        rewrite div_even. destruct (sqrt_spec' p) as [l0 l1]. nia.
      * rewrite er. rewrite again_r. rewrite <- (mul_assoc 2).
        rewrite div_even. destruct (sqrt_spec' p) as [l0 l1]. nia.
    + rewrite eq. rewrite div_odd.
      destruct (exist_even_odd q) as [r [er | er]].
      * rewrite er. rewrite <- (mul_assoc 2).
        rewrite div_even. destruct (sqrt_spec' p) as [l0 l1]. nia.
      * rewrite er. rewrite again_r. rewrite <- (mul_assoc 2).
        rewrite div_even. destruct (sqrt_spec' p) as [l0 l1]. nia. Qed.

(** The function [tri] provides bounds
    for inverses of [untri] and [untri_up]. *)

Theorem tri_untri_untri_up (n : N) : tri (untri n) <= n <= tri (untri_up n).
Proof.
  split.
  - apply tri_untri.
  - apply tri_untri_up. Qed.

(** An inverse of the generating function, with a remainder. *)

Definition untri_rem (n : N) : N * N :=
  let (s, t) := sqrtrem (succ (shiftl n 3)) in
  let (q, r) := div_eucl (pred s) 2 in
  (q, shiftr (t + r * pred (shiftl s 1)) 3).

Lemma untri_rem_eqn (n : N) : untri_rem n =
  let (s, t) := sqrtrem (1 + 8 * n) in
  let (q, r) := div_eucl (s - 1) 2 in
  (q, (t + r * (2 * s - 1)) / 8).
Proof.
  cbv [untri_rem].
  arithmetize. destruct_sqrtrem_fresh.
  arithmetize. destruct_div_eucl_fresh.
  arithmetize. reflexivity. Qed.

(** The function [untri_rem] can be defined in terms of [tri] and [untri]. *)

Lemma untri_rem_tri_untri (n : N) : untri_rem n = (untri n, n - tri (untri n)).
Proof.
  rewrite untri_rem_eqn. rewrite untri_eqn. rewrite tri_eqn.
  repeat rewrite <- sqrtrem_sqrt.
  cbv [fst snd].
  destruct_sqrtrem s t est es e0st l1st.
  repeat rewrite <- (div_eucl_div (s - 1) 2).
  cbv [fst snd].
  destruct_div_eucl q r eqr eq e0qr l1qr.
  f_equal.
  enough ((t + r * (2 * s - 1)) / 8 + q * (1 + q) / 2 = n) by admit.
  rewrite <- eq.
  replace n with ((s * s + t - 1) / 8).
  2: { rewrite <- e0st. replace (1 + 8 * n - 1) with (n * 8) by lia.
  rewrite div_mul by lia. lia. }
  rewrite <- div_add by lia.
  assert (or : r = 0 \/ r = 1) by lia.
  destruct or as [er | er]; subst r; arithmetize.
  destruct (exist_even_odd (s - 1)) as [r [er | er]].
  - rewrite er. rewrite div_even.
    destruct (exist_even_odd r) as [r' [er' | er']].
    + rewrite er'.
      replace (2 * r' * (1 + 2 * r'))
      with (2 * (r' * (1 + 2 * r'))) by lia.
      rewrite div_even.
      replace (8 * (r' * (1 + 2 * r')))
      with (2 * (2 * (2 * r')) + (2 * (2 * r')) * (2 * (2 * r'))) by lia.
      rewrite <- er'. rewrite <- er.
      replace (2 * (s - 1) + (s - 1) * (s - 1))
      with (s * s - 1) by nia. (* ! *)
      rewrite add_sub_assoc by nia.
      rewrite add_comm. reflexivity.
    + rewrite er'.
      replace ((1 + 2 * r') * (1 + (1 + 2 * r')))
      with (2 * ((1 + 2 * r') * (1 + r'))) by lia.
      rewrite div_even.
      rewrite <- er'. admit.
  - Admitted.

(** The function [untri_rem] is an inverse of [tri]. *)

Theorem untri_rem_tri (n : N) : untri_rem (tri n) = (n, 0).
Proof. rewrite untri_rem_tri_untri. rewrite untri_tri. f_equal. lia. Qed.

(** The function [tri] is an inverse of [untri_rem]. *)

Theorem tri_untri_rem (n : N) : prod_uncurry (add o tri) (untri_rem n) = n.
Proof.
  rewrite untri_rem_tri_untri.
  cbv [prod_uncurry fst snd compose].
  rewrite add_sub_assoc.
  - lia.
  - apply tri_untri. Qed.

(** A partial inverse of the generating function. *)

Definition untri_error (n : N) : option N :=
  let (s, t) := sqrtrem (succ (shiftl n 3)) in
  if t =? 0 then Some (shiftr (pred s) 1) else None.

Arguments untri_error _ : assert.

Lemma untri_error_eqn (n : N) : untri_error n =
  let (s, t) := sqrtrem (1 + 8 * n) in
  if t =? 0 then Some ((s - 1) / 2) else None.
Proof.
  cbv [untri_error].
  arithmetize. destruct_sqrtrem_fresh.
  arithmetize. reflexivity. Qed.

(** The function [untri_error] can be defined in terms of [untri_rem]. *)

Lemma untri_error_untri_rem (n : N) :
  untri_error n =
  let (u, v) := untri_rem n in
  if v =? 0 then Some u else None.
Proof.
  pose proof tri_untri n as l. revert l.
  rewrite untri_error_eqn. rewrite untri_rem_tri_untri.
  rewrite untri_eqn. rewrite tri_eqn.
  rewrite <- sqrtrem_sqrt.
  cbv [fst snd].
  destruct_sqrtrem s t est es e0st l1st.
  rewrite <- (div_eucl_div (s - 1) 2).
  cbv [fst snd].
  destruct_div_eucl q r eqr eq e0qr l1qr.
  intros l. replace (n - q * (1 + q) / 2 =? 0) with (n =? q * (1 + q) / 2).
  2:{ destruct (eqb_spec n (q * (1 + q) / 2)), (eqb_spec (n - q * (1 + q) / 2) 0); reflexivity || lia. }
  assert (or : r = 0 \/ r = 1) by lia. clear l1qr.
  destruct or as [er | er]; subst r.
  - arithmetize. destruct (eqb_spec t 0) as [et | ft].
    + subst t. arithmetize.
      replace n with ((1 + 8 * n - 1) / 8) by lia || admit.
      rewrite e0st.
      replace s with (s - 1 + 1) by lia || admit.
      rewrite e0qr.
      replace ((2 * q + 1) * (2 * q + 1) - 1) with (4 * q * (1 + q)) by lia.
      replace 8 with (2 * 2 * 2) by lia.
      replace 4 with (2 * 2) by lia.
      repeat rewrite <- (mul_assoc _).
      repeat rewrite <- div_div by lia.
      repeat rewrite div_even. rewrite eqb_refl. reflexivity.
    + idtac.
      (** Need to know [8 <= t]. *)
      admit.
  - arithmetize. destruct (eqb_spec t 0) as [et | ft].
    + subst t.
      (** Need to know [s <= 2]. *)
      admit.
    + idtac.
      admit. Admitted.

(** The function [untri_error] is a lifted inverse of [tri]. *)

Theorem untri_error_tri (n : N) : untri_error (tri n) = Some n.
Proof. rewrite untri_error_untri_rem. rewrite untri_rem_tri. reflexivity. Qed.

(** A lifting of the function [tri] is an inverse of [untri_error]. *)

Theorem tri_untri_error (n p : N)
  (e : option_map tri (untri_error n) = Some p) : n = p.
Proof.
  rewrite untri_error_untri_rem in e.
  rewrite untri_rem_tri_untri in e.
  destruct (eqb_spec (n - tri (untri n)) 0) as [e' | f'].
  - cbv [option_map] in e.
    injection e; clear e; intros e.
    rewrite <- e. clear e. pose proof sub_add _ _ (tri_untri n) as e''. lia.
  - cbv [option_map] in e. inversion e. Qed.
