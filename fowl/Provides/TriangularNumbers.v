(** A generating function for triangular numbers and
    three variations of its inverse. *)

From Coq Require Import
  Lia Lists.List NArith.NArith.
From Maniunfold.Provides Require Export
  OptionTheorems ProductTheorems.

Import N.

Local Open Scope N_scope.

(** An experiment in tactical number theory! *)

Ltac reduce_1 p0 f :=
  match goal with
  | |- context c [f ?x] => p0 x;
    match eval cbv in (f x) with
    | ?q => let r := context c [q] in change r
    end
  | h : context c [f ?x ?y] |- _ => p0 x;
    match eval cbv in (f x y) with
    | ?q => let r := context c [q] in change r in h
    end
  end.

Ltac reduce_2 p0 p1 f :=
  match goal with
  | |- context c [f ?x ?y] => p0 x; p1 y;
    match eval cbv in (f x y) with
    | ?q => let r := context c [q] in change r
    end
  | h : context c [f ?x ?y] |- _ => p0 x; p1 y;
    match eval cbv in (f x y) with
    | ?q => let r := context c [q] in change r in h
    end
  end.

Ltac commute_2_0 p f e :=
  match goal with
  | |- context c [f ?x ?y] => assert_fails (idtac; p x); p y;
    let r := context c [f y x] in
    let f := fresh in enough (f : r) by (rewrite (e x y); exact f)
  | h : context c [f ?x ?y] |- _ => assert_fails (idtac; p x); p y;
    let r := context c [f y x] in
    let f := fresh in rewrite (e x y) in h
  end.

Ltac commute_2_1 p f e :=
  match goal with
  | |- context c [f ?x ?y] => p x; assert_fails (idtac; p y);
    let r := context c [f y x] in
    let f := fresh in enough (f : r) by (rewrite (e x y); exact f)
  | h : context c [f ?x ?y] |- _ => p x; assert_fails (idtac; p y);
    let r := context c [f y x] in
    let f := fresh in rewrite (e x y) in h
  end.

Ltac is_positive n :=
  match n with
  | xI ?p => is_positive p
  | xO ?p => is_positive p
  | xH => idtac
  | _ => fail "Not a value"
  end.

Ltac is_N n :=
  match n with
  | N0 => idtac
  | Npos ?p => is_positive p
  | _ => fail "Not a value"
  end.

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
  repeat rewrite pow_0_r in *;
  (** Reduce [succ], [_ + _], [_ * _], [_ ^ _], [pred], [_ - _] and [_ / _]. *)
  repeat reduce_1 is_N succ;
  repeat reduce_2 is_N is_N add;
  repeat reduce_2 is_N is_N mul;
  repeat reduce_2 is_N is_N pow;
  repeat reduce_1 is_N pred;
  repeat reduce_2 is_N is_N sub;
  repeat reduce_2 is_N is_N div;
  (** Commute [_ + _] and [_ * _]. *)
  repeat commute_2_0 is_N add add_comm;
  repeat commute_2_0 is_N mul mul_comm.

(** A specialization of [seq] for [positive]. *)

Fixpoint Pos_seq (n : positive) (p : nat) : list positive :=
  match p with
  | O => nil
  | S q => n :: Pos_seq (Pos.succ n) q
  end.

(** A specialization of [seq] for [N]. *)

Fixpoint N_seq (n : N) (p : nat) : list N :=
  match p with
  | O => nil
  | S q => n :: N_seq (succ n) q
  end.

(** Case analysis for the remainder of division by two. *)

Lemma lt_2_cases (n : N) (l : n < 2) : n = 0 \/ n = 1.
Proof. lia. Qed.

(** A richer specification for [div_eucl].
    Analogous in structure to [sqrtrem_spec]. *)

Lemma div_eucl_spec' (n p : N) :
  let (q, r) := div_eucl n p in n = p * q + r /\ (p <> 0 -> r < p).
Proof.
  destruct n as [| n'], p as [| p']; cbv [div_eucl] in *; try lia.
  pose proof pos_div_eucl_spec n' (pos p') as en'p'.
  pose proof pos_div_eucl_remainder n' (pos p') as ln'p'.
  destruct (pos_div_eucl n' (pos p')) as [q r]; cbv [snd] in *; lia. Qed.

(** What it means to be even or odd. *)

Lemma factor_even_odd (n : N) : exists p : N, n = 2 * p \/ n = 1 + 2 * p.
Proof.
  induction n as [| q ei] using peano_ind.
  - exists 0. lia.
  - arithmetize. destruct ei as [r [e | e]].
    + exists (q / 2). subst q. right.
      replace (2 * r) with (r * 2) by lia.
      rewrite div_mul by lia. lia.
    + exists ((1 + q) / 2). subst q. left.
      replace (1 + (1 + 2 * r)) with (2 * (1 + r)) by lia.
      replace (2 * (1 + r)) with ((1 + r) * 2) by lia.
      rewrite div_mul by lia. lia. Qed.

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

Arguments untri_up _ : assert.

Lemma untri_up_eqn (n : N) : untri_up n =
  if n =? 0 then 0 else 1 + (sqrt (1 + 8 * (n - 1)) - 1) / 2.
Proof.
  destruct (eqb_spec n 0) as [e | f].
  - rewrite e. cbv [untri_up]. reflexivity.
  - destruct n as [| p].
    + contradiction.
    + cbv [untri_up]. rewrite pos_pred_spec. arithmetize.
      rewrite untri_eqn. reflexivity. Qed.

Set Warnings "-unsupported-attributes".

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
  rewrite (add_assoc 1 1 n).
  rewrite (add_1_l 1).
  rewrite <- two_succ.
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

(** Replace [sqrtrem] with its specification. *)

Ltac destruct_sqrtrem :=
  match goal with
  | |- context [let (a, b) := sqrtrem ?x in _] =>
    let fa := fresh a in let fb := fresh b in
    let faab := fresh "a" fa fb in pose proof sqrtrem_spec x as faab;
    let fe := fresh "e" fa fb in destruct (sqrtrem x) as [fa fb] eqn : fe;
    let fen := fresh "en" fa fb in let fl := fresh "l" fa fb in
    destruct faab as [fen fl]
  end.

(** Replace [div_eucl] with its specification. *)

Ltac destruct_div_eucl :=
  match goal with
  | |- context [let (a, b) := div_eucl ?x ?y in _] =>
    let fa := fresh a in let fb := fresh b in
    let faab := fresh "a" fa fb in pose proof div_eucl_spec' x y as faab;
    let fe := fresh "e" fa fb in destruct (div_eucl x y) as [fa fb] eqn : fe;
    let fen := fresh "en" fa fb in let fl := fresh "l" fa fb in
    destruct faab as [fen fl]
  end.

Lemma untri_rem_eqn (n : N) : untri_rem n =
  let ((* square root *) s, (* remains *) r) := sqrtrem (1 + 8 * n) in
  let ((* quotient *) q, (* remainder *) e) := div_eucl (s - 1) 2 in
  (q, (r + e * (2 * s - 1)) / 8).
Proof.
  cbv [untri_rem]. arithmetize. destruct_sqrtrem.
  arithmetize. destruct_div_eucl. arithmetize. f_equal. Qed.

Theorem untri_rem_tri (n : N) : untri_rem (tri n) = (n, 0).
Proof.
  rewrite untri_rem_eqn.
  destruct_sqrtrem.
  destruct_div_eucl.
  specialize (lqe ltac:(lia)).
  pose proof (lt_2_cases e lqe) as oe.
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
  cbv [prod_uncurry compose].
  rewrite tri_eqn.
  rewrite untri_rem_eqn.
  destruct_sqrtrem.
  destruct_div_eucl.
  cbv [fst snd].
  specialize (lqe ltac:(lia)).
  pose proof (lt_2_cases e lqe) as oe.
  clear lqe. Admitted.

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
