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

(** TODO Move these missing instances elsewhere. *)

Instance mul_wd' :
  Morphisms.Proper (Morphisms.respectful le (Morphisms.respectful le le)) mul.
Proof.
  intros n p l n' p' l'. apply mul_le_mono; [lia |]. lia. Qed.

Instance add_wd' :
  Morphisms.Proper (Morphisms.respectful le (Morphisms.respectful le le)) add.
Proof.
  intros n p l n' p' l'. apply add_le_mono; [lia |]. lia. Qed.

Instance div2_wd' :
  Morphisms.Proper (Morphisms.respectful le le) div2.
Proof.
  intros n p l. repeat rewrite div2_div. apply div_le_mono; [lia |]. lia. Qed.

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

(** Generating function preserves zeroness. *)

Lemma tri_eq_0 (n : N) (e : tri n = 0) : n = 0.
Proof.
  rewrite tri_eqn in e. destruct n as [| p _] using peano_ind.
  - reflexivity.
  - exfalso. arithmetize.
    replace ((1 + p) * (2 + p)) with (1 * 2 + p * (3 + p)) in e by lia.
    rewrite div_add_l in e by lia.
    remember (p * (3 + p) / 2) as q eqn : eq. lia. Qed.

(** Generating function preserves nonzeroness. *)

Lemma tri_neq_0 (n : N) (e : tri n <> 0) : n <> 0.
Proof.
  rewrite tri_eqn in e. destruct n as [| p _] using peano_ind.
  - arithmetize. lia.
  - lia. Qed.

Theorem untri_tri (n : N) : untri (tri n) = n.
Proof.
  rewrite tri_eqn, untri_eqn.
  replace (8 * (n * (1 + n) / 2)) with (4 * (2 * (n * (1 + n) / 2))) by lia.
  rewrite <- divide_div_mul_exact; [| lia |].
  - rewrite div_even.
    replace (1 + 4 * (n * (1 + n))) with ((1 + 2 * n) * (1 + 2 * n)) by lia.
    rewrite sqrt_square.
    replace (1 + 2 * n - 1) with (2 * n) by lia.
    rewrite div_even. reflexivity.
  - apply mod_divide; [lia |]. apply mod_mul_consecutive. Qed.

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

Lemma tri_untri (n : N) : tri (untri n) <= n.
Proof.
  rewrite tri_eqn, untri_eqn.
  remember (1 + 8 * n) as p eqn : ep.
  destruct (exist_even_odd (sqrt p - 1)) as [q [eq | eq]].
  - rewrite eq. rewrite div_even.
    destruct (exist_even_odd q) as [r [er | er]].
    + rewrite er.
      replace (2 * r * (1 + 2 * r)) with (2 * (r * (1 + 2 * r))) by lia.
      rewrite div_even. destruct (sqrt_spec' p) as [l0 l1]. nia.
    + rewrite er.
      replace ((1 + 2 * r) * (1 + (1 + 2 * r)))
      with (2 * ((1 + 2 * r) * (1 + r))) by lia.
      rewrite div_even. destruct (sqrt_spec' p) as [l0 l1]. nia.
  - rewrite eq. rewrite div_odd.
    destruct (exist_even_odd q) as [r [er | er]].
    + rewrite er.
      replace (2 * r * (1 + 2 * r)) with (2 * (r * (1 + 2 * r))) by lia.
      rewrite div_even. destruct (sqrt_spec' p) as [l0 l1]. nia.
    + rewrite er.
      replace ((1 + 2 * r) * (1 + (1 + 2 * r)))
      with (2 * ((1 + 2 * r) * (1 + r))) by lia.
      rewrite div_even. destruct (sqrt_spec' p) as [l0 l1]. nia. Qed.

Lemma tri_untri_up (n : N) : n <= tri (untri_up n).
Proof.
  rewrite tri_eqn, untri_up_eqn.
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
      * rewrite er.
        replace (2 * r * (1 + 2 * r)) with (2 * (r * (1 + 2 * r))) by lia.
        rewrite div_even. destruct (sqrt_spec' p) as [l0 l1]. nia.
      * rewrite er.
        replace ((1 + 2 * r) * (1 + (1 + 2 * r)))
        with (2 * ((1 + 2 * r) * (1 + r))) by lia.
        rewrite div_even. destruct (sqrt_spec' p) as [l0 l1]. nia.
    + rewrite eq. rewrite div_odd.
      destruct (exist_even_odd q) as [r [er | er]].
      * rewrite er.
        replace (2 * r * (1 + 2 * r)) with (2 * (r * (1 + 2 * r))) by lia.
        rewrite div_even. destruct (sqrt_spec' p) as [l0 l1]. nia.
      * rewrite er.
        replace ((1 + 2 * r) * (1 + (1 + 2 * r)))
        with (2 * ((1 + 2 * r) * (1 + r))) by lia.
        rewrite div_even. destruct (sqrt_spec' p) as [l0 l1]. nia. Qed.

Theorem tri_untri_untri_up (n : N) : tri (untri n) <= n <= tri (untri_up n).
Proof.
  split.
  - apply tri_untri.
  - apply tri_untri_up. Qed.

(** Addition and multiplication are equally fast wrt both argument sizes,
    but we pretend the first one should be smaller and "more constant".
    Usually the choice is obvious,
    but here [r <= e * (2 * s - 1)] by a very slim margin
    (approaching 0 % from above). *)

(** Inverse of generating function, with a remainder.

    The remainder can be derived from [n - tri (untri n)]
    by eliminating variables via [sqrtrem_spec] and [div_eucl_spec]. *)

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

(** TODO This is tricky. *)

Lemma untri_rem_tri_untri (n : N) : untri_rem n = (untri n, n - tri (untri n)).
Proof.
  rewrite untri_rem_eqn.
  destruct_sqrtrem s t est es e0st l1st.
  destruct_div_eucl q r eqr eq e0qr l1qr.
  rewrite untri_eqn. rewrite tri_eqn.
  f_equal.
  - rewrite <- eq. rewrite <- es. reflexivity.
  - remember (1 + 8 * n) as p eqn : ep.
    (* rewrite <- div_add_l by lia.
    assert (fp : sqrt p <> 0).
    { destruct (sqrt_spec' p) as [l0 l1]. nia. }
    replace (1 * 2 + (sqrt p - 1)) with (1 + sqrt p) by lia. *)
    destruct (exist_even_odd (sqrt p - 1)) as [u [eu | eu]].
    + rewrite eu. rewrite div_even.
      destruct (exist_even_odd u) as [v [ev | ev]].
      * rewrite ev.
        replace (2 * v * (1 + 2 * v)) with (2 * (v * (1 + 2 * v))) by lia.
        rewrite div_even.
        (** Need to know [r' ^ 2 = r']. *)
        destruct (sqrt_spec' p) as [l0 l1]. admit.
      * rewrite ev.
        replace ((1 + 2 * v) * (1 + (1 + 2 * v)))
        with (2 * ((1 + 2 * v) * (1 + v))) by lia.
        rewrite div_even.
        destruct (sqrt_spec' p) as [l0 l1]. admit. Admitted.

Theorem untri_rem_tri (n : N) : untri_rem (tri n) = (n, 0).
Proof. rewrite untri_rem_tri_untri. rewrite untri_tri. f_equal. lia. Qed.

Theorem tri_untri_rem (n : N) : prod_uncurry (add o tri) (untri_rem n) = n.
Proof.
  rewrite untri_rem_tri_untri.
  cbv [prod_uncurry fst snd compose].
  rewrite add_sub_assoc.
  - lia.
  - apply tri_untri. Qed.

(** Inverse of generating function, partial. *)

Definition untri_error (n : N) : option N :=
  let (s, t) := sqrtrem (succ (shiftl n 3)) in
  if t =? 0 then Some (shiftr (pred s) 1) else None.

Arguments untri_error _ : assert.

Lemma untri_error_eqn (n : N) : untri_error n =
  let (s, t) := sqrtrem (1 + 8 * n) in
  if t =? 0 then Some ((s - 1) / 2) else None.
Proof.
  cbv [untri_error]. arithmetize.
  destruct_sqrtrem s t est es e0st l1st.
  arithmetize. reflexivity. Qed.

(** TODO This is tricky. *)

Lemma untri_error_untri_rem (n : N) :
  untri_error n =
  let (u, v) := untri_rem n in
  if v =? 0 then Some u else None.
Proof.
  rewrite untri_error_eqn. rewrite untri_rem_eqn.
  destruct_sqrtrem s t est es e0st l1st.
  destruct_div_eucl q r eqr eq e0qr l1qr.
  rewrite eq.
  assert (or : r = 0 \/ r = 1) by lia. clear l1qr.
  destruct or as [er | er]; subst r.
  - arithmetize. destruct (eqb_spec t 0) as [et | ft].
    + subst t. reflexivity.
    + idtac.
      (** Need to know [8 <= t]. *)
      admit.
  - arithmetize. destruct (eqb_spec t 0) as [et | ft].
    + subst t. arithmetize.
      replace (2 * s - 1) with (1 + 2 * (1 + s)) by lia.
      replace 8 with (2 * 4) by lia.
      rewrite <- div_div by lia.
      rewrite div_odd.
      (** Need to know [s <= 2]. *)
      admit.
    + idtac.
      admit. Admitted.

Theorem untri_error_tri (n : N) : untri_error (tri n) = Some n.
Proof. rewrite untri_error_untri_rem. rewrite untri_rem_tri. reflexivity. Qed.

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
