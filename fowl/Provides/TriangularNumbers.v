From Coq Require Import
  Lia Lists.List NArith.NArith.
From Maniunfold.Provides Require Export
  OptionTheorems ProductTheorems.

Import ListNotations N.

Local Open Scope N_scope.

Ltac arithmetize :=
  (** Eliminate [shiftl 0 _]. *)
  repeat rewrite shiftl_0_l in *;
  (** Eliminate [shiftl _ 0]. *)
  repeat rewrite shiftl_0_r in *;
  (** Eliminate [shiftl 1 _]. *)
  repeat rewrite shiftl_1_l in *;
  (** Eliminate [shiftl _ _]. *)
  repeat rewrite shiftl_mul_pow2 in *;
  (** Eliminate [double _]. *)
  repeat rewrite double_spec in *;
  (** Eliminate [succ]. *)
  repeat rewrite <- add_1_l in *;
  (** Eliminate [shiftr 0 _]. *)
  repeat rewrite shiftr_0_l in *;
  (** Eliminate [shiftr _ 0]. *)
  repeat rewrite shiftr_0_r in *;
  (** Eliminate [shiftr _ 1]. *)
  repeat rewrite <- div2_spec in *;
  (** Eliminate [shiftr _ _]. *)
  repeat rewrite shiftr_div_pow2 in *;
  (** Eliminate [div2 _]. *)
  repeat rewrite div2_div in *;
  (** Eliminate [pred]. *)
  repeat rewrite <- sub_1_r in *;
  (** Eliminate [1 ^ _]. *)
  repeat rewrite pow_1_l in *;
  (** Eliminate [_ ^ 1]. *)
  repeat rewrite pow_1_r in *;
  (** Eliminate [0 ^ _]. *)
  repeat rewrite pow_0_r in *.

Local Definition seq (n p : N) : list N :=
  map of_nat (seq (to_nat n) (to_nat p)).

(** Triangular number function, sequence A000217. *)

Definition tri (n : N) : N :=
  (* n * (1 + n) / 2 *)
  shiftr (n * succ n) 1.

Arguments tri _ : assert.

(** Inverse of the triangular number function, rounding down, A003056. *)

Definition untri (n : N) : N :=
  (* (sqrt (1 + 8 * n) - 1) / 2 *)
  shiftr (pred (sqrt (succ (shiftl n 3)))) 1.

Arguments untri _ : assert.

Lemma tri_subterm_Even (n : N) : Even (n * (1 + n)).
Proof.
  apply even_spec. rewrite even_mul. apply Bool.orb_true_intro.
  destruct (Even_or_Odd n) as [E | E].
  - left. apply even_spec. assumption.
  - right. rewrite add_1_l. rewrite even_succ. apply odd_spec. assumption. Qed.

Lemma succ_mod (n p : N) (l : 1 < n) : (succ p) mod n = succ (p mod n) mod n.
Proof.
  arithmetize.
  rewrite add_mod by lia. rewrite mod_1_l by lia. reflexivity. Qed.

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
  rewrite (add_assoc 1 1 n).
  rewrite (add_1_l 1).
  rewrite <- two_succ.
  rewrite (mul_add_distr_l (1 + n) 2 n).
  rewrite (div_add_l (1 + n) 2 ((1 + n) * n)).
  - rewrite (mul_comm (1 + n) n). reflexivity.
  - rewrite two_succ. apply (neq_succ_0 1). Qed.

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
    replace (2 ^ 3) with 8 by admit.
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

Theorem tri_untri (n : N) : tri (untri n) <= n.
Proof. Admitted.

(** Inverse of the triangular number function, with remainder.

    The remainder is easily derived from [n - tri q]
    by eliminating variables via [sqrtrem_spec] and [div_eucl_spec]. *)

(** Addition and multiplication are equally fast wrt both argument sizes,
    but we pretend the first one should be smaller and "more constant".
    Usually the choice is obvious,
    but here [r <= e * (2 * s - 1)] by a very slim margin
    (approaching 0 %, but from above). *)

Definition untri_rem (n : N) : N * N :=
  (* let ((* square root *) s, (* remains *) r) := sqrtrem (1 + 8 * n) in
  let ((* quotient *) q, (* remainder *) e) := div_eucl (s - 1) 2 in
  (q, (r + e * (2 * s - 1)) / 8) *)
  let (s, r) := sqrtrem (succ (shiftl n 3)) in
  let (q, e) := div_eucl (pred s) 2 in
  (q, shiftr (r + e * pred (shiftl s 1)) 3).

Lemma div_eucl_spec' (n p : N) :
  let (q, r) := div_eucl n p in n = p * q + r /\ (p <> 0 -> r < p).
Proof.
  destruct n as [| n'], p as [| p']; cbv [div_eucl] in *; try lia.
  pose proof pos_div_eucl_spec n' (pos p') as en'p'.
  pose proof pos_div_eucl_remainder n' (pos p') as ln'p'.
  destruct (pos_div_eucl n' (pos p')) as [q r]; cbv [snd] in *; lia. Qed.

Lemma lt_2 (n : N) (l : n < 2) : n = 0 \/ n = 1.
Proof. lia. Qed.

Theorem untri_rem_tri (n : N) : untri_rem (tri n) = (n, 0).
Proof.
  cbv [untri_rem tri].
  match goal with
  | |- context [let (a, b) := sqrtrem ?x in _] =>
    let fa := fresh "a" a b in pose proof sqrtrem_spec x as fa;
    let fe := fresh "e" a b in destruct (sqrtrem x) as [a b] eqn : fe;
    let fen := fresh "en" a b in let fl := fresh "l" a b in
    destruct fa as [fen fl]
  end.
  match goal with
  | |- context [let (a, b) := div_eucl ?x ?y in _] =>
    let fa := fresh "a" a b in pose proof div_eucl_spec' x y as fa;
    let fe := fresh "e" a b in destruct (div_eucl x y) as [a b] eqn : fe;
    let fen := fresh "en" a b in let fl := fresh "l" a b in
    destruct fa as [fen fl]
  end.
  arithmetize.
  specialize (lqe ltac:(lia)).
  pose proof (lt_2 e lqe) as oe.
  clear lqe.
  destruct oe as [e0 | e1]; subst e.
  - f_equal.
    + enough (1 + (2 * q + 0) - 2 * n = 1) by lia.
      rewrite <- enqe.
      enough (s = 1 + 2 * n) by lia.
      apply (pow_inj_l _ _ 2); [lia |].
      rewrite pow_2_r.
      enough (s * s + r = (1 + 2 * n) ^ 2 + r) by lia.
      rewrite <- ensr. admit.
    + replace (r + 0 * (s * 2 - 1)) with r by lia.
      apply le_0_r. admit.
    (* + enough (1 + (2 * q + e) - 2 * n = 1 + e) by lia.
      rewrite <- aqe.
      enough (s = 1 + e + 2 * n) by lia.
      apply (pow_inj_l _ _ 2); [lia |].
      rewrite pow_2_r.
      enough (s * s + r = (1 + e + 2 * n) ^ 2 + r) by lia.
      rewrite <- ensr.
      rewrite pow_2_r.
      replace 3 with (succ 2) by lia; rewrite pow_succ_r'. admit. *)
  - f_equal.
    + admit.
    + admit. Admitted.

Theorem tri_untri_rem (n : N) : prod_uncurry (add o tri) (untri_rem n) = n.
Proof.
  cbv [prod_uncurry compose tri untri_rem].
  match goal with
  | |- context [let (a, b) := sqrtrem ?x in _] =>
    let fa := fresh "a" a b in pose proof sqrtrem_spec x as fa;
    let fe := fresh "e" a b in destruct (sqrtrem x) as [a b] eqn : fe;
    let fen := fresh "en" a b in let fl := fresh "l" a b in
    destruct fa as [fen fl]
  end.
  match goal with
  | |- context [let (a, b) := div_eucl ?x ?y in _] =>
    let fa := fresh "a" a b in pose proof div_eucl_spec' x y as fa;
    let fe := fresh "e" a b in destruct (div_eucl x y) as [a b] eqn : fe;
    let fen := fresh "en" a b in let fl := fresh "l" a b in
    destruct fa as [fen fl]
  end.
  cbv [fst snd].
  arithmetize.
  specialize (lqe ltac:(lia)).
  pose proof (lt_2 e lqe) as oe.
  clear lqe. Admitted.

(** Inverse of the triangular number function, partial. *)

Definition untri_error (n : N) : option N :=
  (* let ((* square root *) s, (* remains *) r) := sqrtrem (1 + 8 * n) in
  if r =? 0 then Some ((s - 1) / 2) else None *)
  let (s, r) := sqrtrem (succ (shiftl n 3)) in
  if r =? 0 then Some (shiftr (pred s) 1) else None.

Arguments untri_error _ : assert.

Lemma tri_untri_error_succ (n : N) :
  option_map tri (untri_error (succ n)) =
  option_map (succ o tri) (untri_error n).
Proof. Admitted.

Theorem untri_error_tri (n : N) : untri_error (tri n) = Some n.
Proof.
  induction n as [| p eip] using peano_ind.
  - auto.
  - cbv [untri_error tri] in *.
    repeat match goal with
    | |- context [sqrtrem ?x] => destruct (sqrtrem x) as [ss sr]
    | _ : context [sqrtrem ?x] |- _ => destruct (sqrtrem x) as [s r]
    end.
    repeat match goal with
    | |- context [?x =? ?y] => destruct (eqb_spec x y) as [esp | fsp]
    | _ : context [?x =? ?y] |- _ => destruct (eqb_spec x y) as [ep | fp]
    end.
    + injection eip; clear eip; intros eip.
      f_equal. admit.
    + inversion eip.
    + injection eip; clear eip; intros eip.
      exfalso. apply fsp; clear fsp. admit.
    + inversion eip. Admitted.

Lemma factor_even_odd (n : N) : exists p : N, n = 2 * p \/ n = 1 + 2 * p.
Proof.
  induction n as [| q ei] using peano_ind.
  - exists 0. lia.
  - destruct ei as [r [e | e]].
    + exists (q / 2). subst q. right.
      replace (2 * r) with (r * 2) by lia.
      rewrite div_mul by lia. lia.
    + exists ((1 + q) / 2). subst q. left.
      replace (1 + (1 + 2 * r)) with (2 * (1 + r)) by lia.
      replace (2 * (1 + r)) with ((1 + r) * 2) by lia.
      rewrite div_mul by lia. lia. Qed.

Theorem tri_untri_error (n p : N)
  (e : option_map tri (untri_error n) = Some p) :
  n = p.
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
      match goal with
      | |- context [let (a, b) := sqrtrem ?x in _] =>
        let fa := fresh "a" a b in pose proof sqrtrem_spec x as fa;
        let fe := fresh "e" a b in destruct (sqrtrem x) as [a b] eqn : fe;
        let fen := fresh "en" a b in let fl := fresh "l" a b in
        destruct fa as [fen fl]
      end.
      destruct (eqb_spec r 0) as [e | f].
      * cbv [option_map] in *. f_equal. arithmetize.
        assert (enp' : (1 + (s - 1) / 2 * (1 + (s - 1) / 2) / 2) = p)
        by now inversion enp.
        rewrite <- enp'.
        pose proof factor_even_odd (s - 1) as eo.
        destruct eo as [t [eo | eo]].
        -- rewrite eo.
          repeat rewrite (mul_comm 2 _). rewrite div_mul by lia.
          remember (t * (1 + t) / 2) as u eqn : eu.
          lia.
        -- rewrite eo.
          remember ((1 + 2 * t) / 2 * (1 + (1 + 2 * t) / 2) / 2) as u eqn : eu.
          lia.
      * inversion enp. Qed.
