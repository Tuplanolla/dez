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

Theorem untri_tri (n : N) : untri (tri n) = n.
Proof.
  rewrite tri_eqn, untri_eqn.
  replace (8 * (n * (1 + n) / 2)) with (4 * (2 * (n * (1 + n) / 2))) by lia.
  rewrite double_mul_even_odd.
  replace (1 + 4 * (n * (1 + n))) with ((1 + 2 * n) * (1 + 2 * n)) by lia.
  rewrite sqrt_square.
  replace (1 + 2 * n - 1) with (n * 2) by lia.
  rewrite div_mul by lia. lia. Qed.

Lemma tri_eq_0 (n : N) (e : tri n = 0) : n = 0.
Proof.
  destruct n as [| p ei] using peano_ind.
  - reflexivity.
  - exfalso. rewrite tri_eqn in *. arithmetize.
    replace ((1 + p) * (2 + p)) with (1 * 2 + p * (3 + p)) in e by lia.
    rewrite div_add_l in e by lia.
    remember (p * (3 + p) / 2) as q eqn : eq. lia. Qed.

Lemma tri_neq_0 (n : N) (e : tri n <> 0) : n <> 0.
Proof.
  destruct n as [| p ei] using peano_ind.
  - rewrite tri_eqn in e. apply e.
  - lia. Qed.

Theorem untri_up_tri (n : N) : untri_up (tri n) = n.
Proof.
  rewrite untri_up_eqn.
  destruct (eqb_spec (tri n) 0) as [e | f].
  - symmetry. apply tri_eq_0. apply e.
  - apply tri_neq_0 in f.
    rewrite tri_eqn.
    replace (8 * (n * (1 + n) / 2 - 1))
    with (4 * (2 * (n * (1 + n) / 2) - 2)) by lia.
    rewrite double_mul_even_odd.
    replace (1 + 4 * (n * (1 + n) - 2))
    with ((1 + 2 * n) * (1 + 2 * n) - 8) by lia.
    Undo. Admitted. (*
    rewrite <- pow_2_r.
    remember (1 + 2 * n) as p eqn : ep.
    repeat rewrite pow_2_r.
    destruct (sqrt_spec' (p * p - 8)) as [l0 l1].
    remember (sqrt ((1 + 2 * n) ^ 2 - 8)) as p eqn : ep.
    enough ((p - 1) / 2 <= n - 1) by lia.
    subst p.
    apply (mul_cancel_l _ _ 2); [lia |].
    mul le
    Check divide_div_mul_exact.
    rewrite <- div_mod; try lia. subst p.
    enough (sqrt ((1 + 2 * n) ^ 2 - 8) = 2 * n - 1) by lia.
    destruct (sqrt_spec' ((1 + 2 * n) ^ 2 - 8)) as [l0 l1].
    rewrite <- sqrt_square.
    apply sqrt_le_mono.
    apply (pow_inj_l _ _ 2); [lia |].
    repeat rewrite <- pow_2_r in *.
    repeat rewrite pow_2_r in *.
    apply le_antisymm.
    + rewrite l0.  lia.
    1 + 4 * n + 4 * n ^ 2 - 8 <= 1 - 4 * n + 4 * n ^ 2
    Search sqrt sub.
    rewrite sqrt_square.
    replace (1 + 2 * n - 1) with (n * 2) by lia.
    rewrite div_mul by lia. lia. Qed.
    remember (sqrt ((1 + 2 * n) ^ 2 - 8) - 1) as p eqn : ep.
    enough (p / 2 = n - 1) by lia.
    destruct (exist_even_odd p) as [q [eq | eq]].
    rewrite eq. *)

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

Theorem tri_untri (n : N) : tri (untri n) <= n.
Proof.
  rewrite tri_eqn, untri_eqn.
  remember (1 + 8 * n) as p eqn : ep.
  destruct (exist_even_odd (sqrt p - 1)) as [q [eq | eq]].
  - rewrite eq. rewrite div_even.
    destruct (exist_even_odd q) as [r [er | er]].
    + rewrite er.
      replace (2 * r * (1 + 2 * r))
      with (r * (1 + 2 * r) * 2) by lia.
      rewrite div_mul by lia. destruct (sqrt_spec' p) as [l0 l1]. lia.
    + rewrite er.
      replace ((1 + 2 * r) * (1 + (1 + 2 * r)))
      with ((1 + 2 * r) * (1 + r) * 2) by lia.
      rewrite div_mul by lia. destruct (sqrt_spec' p) as [l0 l1]. lia.
  - rewrite eq. rewrite div_odd.
    destruct (exist_even_odd q) as [r [er | er]].
    + rewrite er.
      replace (2 * r * (1 + 2 * r))
      with (r * (1 + 2 * r) * 2) by lia.
      rewrite div_mul by lia. destruct (sqrt_spec' p) as [l0 l1]. lia.
    + rewrite er.
      replace ((1 + 2 * r) * (1 + (1 + 2 * r)))
      with ((1 + 2 * r) * (1 + r) * 2) by lia.
      rewrite div_mul by lia. destruct (sqrt_spec' p) as [l0 l1]. lia. Qed.

Theorem tri_untri_up (n : N) : n <= tri (untri_up n).
Proof.
  rewrite tri_eqn, untri_up_eqn.
  destruct (eqb_spec n 0) as [e | f].
  * arithmetize. lia.
  * remember (1 + 8 * (n - 1)) as p eqn : ep.
    destruct (exist_even_odd (sqrt p - 1)) as [q [eq | eq]].
    - rewrite eq. rewrite div_even.
      replace ((1 + q) * (1 + (1 + q))) with (1 * 2 + q * (3 + q)) by lia.
      rewrite div_add_l by lia.
      destruct (exist_even_odd (q * (3 + q))) as [r [er | er]].
      + rewrite er. rewrite div_even. destruct (sqrt_spec' p) as [l0 l1]. nia.
      + rewrite er. rewrite div_odd. destruct (sqrt_spec' p) as [l0 l1]. lia.
    - rewrite eq. rewrite div_odd.
      destruct (exist_even_odd q) as [r [er | er]].
      + rewrite er.
        replace ((1 + 2 * r) * (1 + (1 + 2 * r)))
        with ((1 + 2 * r) * (1 + r) * 2) by lia.
        rewrite div_mul by lia. destruct (sqrt_spec' p) as [l0 l1]. lia.
      + rewrite er.
        replace ((1 + (1 + 2 * r)) * (1 + (1 + (1 + 2 * r))))
        with ((1 + r) * (3 + 2 * r) * 2) by lia.
        rewrite div_mul by lia. destruct (sqrt_spec' p) as [l0 l1]. lia. Qed.

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
      rewrite double_mul_even_odd. enough (r = 0) by lia.
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
