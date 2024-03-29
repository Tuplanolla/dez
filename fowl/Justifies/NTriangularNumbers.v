(** * Triangular Numbers over Binary Natural Numbers *)

From Coq Require Import
  Classes.Morphisms Lia Lists.List NArith.NArith.
From DEZ.Justifies Require Export
  LogicalTheorems NTheorems OptionTheorems ProductTheorems.
From DEZ.Provides Require Import
  DatatypeTactics RewritingTactics.

Import ListNotations N.

#[local] Open Scope N_scope.

(** A generating function.
    Sequence A000217. *)

Equations tri (n : N) : N :=
  tri n := shiftr (n * succ n) 1.

Lemma tri_eqn (n : N) : tri n =
  n * (1 + n) / 2.
Proof. simp tri. arithmetize. auto. Qed.

(** An inverse of the generating function, with a remainder. *)

Equations untri_rem (n : N) : N * N :=
  untri_rem n := let (s, t) := sqrtrem (succ (shiftl n 3)) in
    let (q, r) := div_eucl (pred s) 2 in
    (q, shiftr (t + r * pred (shiftl s 1)) 3).

Lemma untri_rem_eqn (n : N) : untri_rem n =
  let (s, t) := sqrtrem (1 + 8 * n) in
  let (q, r) := div_eucl (s - 1) 2 in
  (q, (t + r * (2 * s - 1)) / 8).
Proof.
  simp untri_rem.
  arithmetize. destruct_sqrtrem s t est es e0st l1st.
  arithmetize. destruct_div_eucl q r eqr eq e0qr l1qr.
  arithmetize. auto.
Qed.

(** A weak inverse of the generating function, rounding down.
    Sequence A003056. *)

Equations untri (n : N) : N :=
  untri n := shiftr (pred (sqrt (succ (shiftl n 3)))) 1.

Lemma untri_eqn (n : N) : untri n =
  (sqrt (1 + 8 * n) - 1) / 2.
Proof. simp untri. arithmetize. auto. Qed.

(** A weak inverse of the generating function, rounding up. *)

Equations untri_up (n : N) : N :=
  untri_up n := match n with
    | N0 => 0
    | Npos p => succ (untri (Pos.pred_N p))
    end.

Lemma untri_up_eqn (n : N) : untri_up n =
  if n =? 0 then 0 else 1 + (sqrt (1 + 8 * (n - 1)) - 1) / 2.
Proof.
  destruct n as [| p].
  - auto.
  - simp untri_up. rewrite pos_pred_spec.
    arithmetize. rewrite untri_eqn. auto.
Qed.

(** A partial inverse of the generating function. *)

Equations untri_error (n : N) : option N :=
  untri_error n := let (s, t) := sqrtrem (succ (shiftl n 3)) in
    if t =? 0 then Some (shiftr (pred s) 1) else None.

Lemma untri_error_eqn (n : N) : untri_error n =
  let (s, t) := sqrtrem (1 + 8 * n) in
  if t =? 0 then Some ((s - 1) / 2) else None.
Proof.
  simp untri_error.
  arithmetize. destruct_sqrtrem s t est es e0st l1st.
  arithmetize. auto.
Qed.

(** TODO These should emerge from the more general inversion stuff. *)

From Coq Require Import Program.Wf.

Program Fixpoint untri_rem' (a n : N) {measure (to_nat n)} : N * N :=
  match untri_error n with
  | Some p => (p, a)
  | None => untri_rem' (1 + a) (n - 1)
  end.
Next Obligation.
  intros a n f x e.
  destruct n as [| p].
  - subst x. inversion e.
  - lia.
Qed.

Program Fixpoint untri_down' (n : N) {measure (to_nat n)} : N :=
  match untri_error n with
  | Some p => p
  | None => untri_down' (n - 1)
  end.
Next Obligation.
  intros n f x e.
  destruct n as [| p].
  - subst x. inversion e.
  - lia.
Qed.

(** This is obvious. *)

Lemma tri_succ (n : N) : tri (1 + n) = (1 + n) + tri n.
Proof.
  do 2 rewrite tri_eqn. destruct (Even_mul_consecutive (1 + n)) as [p ep].
  rewrite ep. rewrite div_Even.
  destruct (Even_mul_consecutive n) as [q eq].
  rewrite eq. rewrite div_Even. lia.
Qed.

(** This is strange. *)

Lemma tri_what (n p : N) : untri (p + tri (n + p)) = n + p.
Proof.
  rewrite untri_eqn, tri_eqn.
  destruct (Even_mul_consecutive (n + p)) as [q eq].
  rewrite eq. rewrite div_Even.
  remember (1 + 8 * (p + q)) as r eqn : er.
  destruct (Even_or_Odd (sqrt r - 1)) as [[s es] | [s es]]; arithmetize.
  - rewrite es. rewrite div_Even.
    destruct (sqrt_spec' r) as [l0 l1]; arithmetize. nia.
  - rewrite es. rewrite div_Odd.
    destruct (sqrt_spec' r) as [l0 l1]; arithmetize. nia.
Qed.

(** This is also strange. *)

Lemma tri_why (a b : N) (l : b <= a) : untri (b + tri a) = a.
Proof.
  assert (x : exists c : N, a = c + b).
  { exists (a - b). lia. }
  destruct x as [c e]. rewrite e. apply tri_what.
Qed.

(** The function [tri] is injective. *)

Lemma tri_inj (n p : N) (e : tri n = tri p) : n = p.
Proof.
  do 2 rewrite tri_eqn in e.
  destruct (Even_mul_consecutive n) as [q eq],
  (Even_mul_consecutive p) as [r er]; arithmetize.
  rewrite eq, er in e. do 2 rewrite div_Even in e. nia.
Qed.

(** The function [tri] is not surjective. *)

Lemma tri_nsurj : exists n : N, forall p : N, n <> tri p.
Proof.
  exists 2. intros p. rewrite tri_eqn.
  destruct p as [| q _] using peano_ind; arithmetize.
  - lia.
  - destruct (Even_mul_consecutive (1 + q)) as [r er]; arithmetize.
    rewrite er. rewrite div_Even. nia.
Qed.

(** The function [tri] is monotonic. *)

Lemma tri_le_mono (n p : N) (l : n <= p) : tri n <= tri p.
Proof.
  do 2 rewrite tri_eqn.
  apply div_le_mono; [lia |].
  apply mul_le_mono; [lia |].
  apply add_le_mono; [lia |]. lia.
Qed.

(** The function [tri] is strictly monotonic. *)

Lemma tri_lt_mono (n p : N) (l : n < p) : tri n < tri p.
Proof.
  assert (l' : n <= p) by lia.
  pose proof tri_le_mono n p l' as l''.
  destruct (eqb_spec (tri n) (tri p)) as [e | f].
  - apply tri_inj in e.
    subst p.
    lia.
  - lia.
Qed.

Local Lemma tri_le_expand_le (n p : N) (l : n <= p) :
  dist n p <= dist (tri n) (tri p).
Proof.
  pose proof tri_le_mono n p l as l'.
  do 2 rewrite dist_eqn.
  destruct (leb_spec n p) as [_ | ?l]; [| lia].
  destruct (leb_spec (tri n) (tri p)) as [_ | ?l]; [| lia].
  revert l'.
  do 2 rewrite tri_eqn.
  destruct (Even_mul_consecutive n) as [q eq],
  (Even_mul_consecutive p) as [r er].
  rewrite eq, er. do 2 rewrite div_Even.
  intros l'.
  nia.
Qed.

(** The function [tri] is expansive. *)

Lemma tri_le_expand (n p : N) : dist n p <= dist (tri n) (tri p).
Proof.
  destruct (leb_spec n p) as [l | l].
  - apply tri_le_expand_le.
    lia.
  - rewrite (dist_comm n p), (dist_comm (tri n) (tri p)).
    apply tri_le_expand_le.
    lia.
Qed.

(** The function [tri] is expansive around zero. *)

Lemma tri_le_expand_0 (n : N) : n <= tri n.
Proof.
  pose proof tri_le_expand n 0 as l.
  cbv [dist] in l.
  change (tri 0) with 0 in l.
  do 2 rewrite max_0_r in l. do 2 rewrite min_0_r in l.
  lia.
Qed.

(** The function [untri] is monotonic. *)

Lemma untri_le_mono (n p : N) (l : n <= p) : untri n <= untri p.
Proof.
  do 2 rewrite untri_eqn.
  apply div_le_mono; [lia |].
  apply sub_le_mono_r.
  apply sqrt_le_mono.
  apply add_le_mono; [lia |].
  apply mul_le_mono; [lia |]. lia.
Qed.

(** The function [untri] is contractive. *)

Lemma untri_le_contract (n p : N) : dist (untri n) (untri p) <= dist n p.
Proof.
  do 2 rewrite untri_eqn.
  remember (1 + 8 * n) as q eqn : eq.
  remember (1 + 8 * p) as r eqn : er. Admitted.

(** The function [untri] is contractive around zero. *)

Lemma untri_le_contract_0 (n : N) : untri n <= n.
Proof.
  rewrite untri_eqn.
  remember (1 + 8 * n) as p eqn : ep.
  destruct (Even_or_Odd (sqrt p - 1)) as [[q eq] | [q eq]]; arithmetize.
  - rewrite eq. rewrite div_Even.
    destruct (sqrt_spec' p) as [l0 l1]; arithmetize. clear l1; nia.
  - rewrite eq. rewrite div_Odd.
    destruct (sqrt_spec' p) as [l0 l1]; arithmetize. clear l1; nia.
Qed.

(** The function [untri] is an inverse of [tri]. *)

Theorem untri_tri (n : N) : untri (tri n) = n.
Proof.
  rewrite untri_eqn, tri_eqn. destruct (Even_mul_consecutive n) as [p ep].
  rewrite ep. rewrite div_Even.
  replace (8 * p) with (4 * (2 * p)) by lia.
  rewrite <- ep. clear ep.
  replace (1 + 4 * (n * (1 + n))) with ((1 + 2 * n) * (1 + 2 * n)) by lia.
  rewrite sqrt_square.
  replace (1 + 2 * n - 1) with (2 * n) by lia.
  rewrite div_Even. auto.
Qed.

(** The function [untri_up] is an inverse of [tri]. *)

Theorem untri_up_tri (n : N) : untri_up (tri n) = n.
Proof.
  rewrite untri_up_eqn.
  destruct (eqb_spec (tri n) 0) as [e | f].
  - apply tri_inj. auto.
  - change 0 with (tri 0) in f. apply f_nequal in f.
    rewrite tri_eqn. destruct (Even_mul_consecutive n) as [p ep].
    rewrite ep. rewrite div_Even.
    remember (1 + 8 * (p - 1)) as q eqn : eq.
    destruct (Even_or_Odd (sqrt q - 1)) as [[r er] | [r er]]; arithmetize.
    + rewrite er. rewrite div_Even.
      destruct (sqrt_spec' q) as [l0 l1]; arithmetize. nia.
    + rewrite er. rewrite div_Odd.
      destruct (sqrt_spec' q) as [l0 l1]; arithmetize. nia.
Qed.

(** The function [tri] provides a lower bound for inverses of [untri]. *)

Lemma tri_untri (n : N) : tri (untri n) <= n.
Proof.
  rewrite tri_eqn, untri_eqn.
  remember (1 + 8 * n) as p eqn : ep.
  destruct (Even_or_Odd (sqrt p - 1)) as [[q eq] | [q eq]]; arithmetize.
  - rewrite eq. rewrite div_Even.
    destruct (Even_mul_consecutive q) as [r er].
    rewrite er. rewrite div_Even.
    destruct (sqrt_spec' p) as [l0 l1]; arithmetize. clear l1; nia.
  - rewrite eq. rewrite div_Odd.
    destruct (Even_mul_consecutive q) as [r er].
    rewrite er. rewrite div_Even.
    destruct (sqrt_spec' p) as [l0 l1]; arithmetize. clear l1; nia.
Qed.

(** The function [tri] provides an upper bound for inverses of [untri]. *)

Lemma tri_untri_up (n : N) : n <= tri (untri_up n).
Proof.
  rewrite tri_eqn, untri_up_eqn.
  destruct (eqb_spec n 0) as [e | f]; arithmetize.
  - lia.
  - remember (1 + 8 * (n - 1)) as p eqn : ep.
    destruct (Even_or_Odd (sqrt p - 1)) as [[q eq] | [q eq]]; arithmetize.
    + rewrite eq. rewrite div_Even.
      destruct (Even_mul_consecutive (1 + q)) as [r er]; arithmetize.
      rewrite er. rewrite div_Even.
      destruct (sqrt_spec' p) as [l0 l1]; arithmetize. clear l0; nia.
    + rewrite eq. rewrite div_Odd.
      destruct (Even_mul_consecutive (1 + q)) as [r er]; arithmetize.
      rewrite er. rewrite div_Even.
      destruct (sqrt_spec' p) as [l0 l1]; arithmetize. clear l0; nia.
Qed.

(** The function [tri] provides bounds
    for inverses of [untri] and [untri_up]. *)

Theorem tri_untri_untri_up (n : N) : tri (untri n) <= n <= tri (untri_up n).
Proof. auto using tri_untri, tri_untri_up. Qed.

(** The function [untri_rem] can be defined in terms of [tri] and [untri]. *)

Lemma untri_rem_tri_untri (n : N) : untri_rem n = (untri n, n - tri (untri n)).
Proof.
  rewrite untri_rem_eqn, tri_eqn, untri_eqn.
  repeat rewrite <- sqrtrem_sqrt. cbv [fst snd].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es l1st.
  repeat rewrite <- (div_eucl_div (s - 1) 2). cbv [fst snd].
  destruct_div_eucl q r eqr eq e0qr l1qr.
  clear eqr eq. f_equal.
  destruct (Even_mul_consecutive q) as [u eu].
  rewrite eu. rewrite div_Even.
  assert (or' : r = 0 \/ r = 1) by lia. clear l1qr.
  (** This case analysis is technically unnecessary,
      but speeds up [nia] considerably. *)
  destruct or' as [er | er]; subst r; arithmetize.
  - change 8 with (2 * (2 * 2)). repeat rewrite <- (div_div _ 2) by lia.
    rename t into t0.
    destruct (Even_or_Odd t0) as [[t1 et1] | [t1 et1]]; arithmetize.
    + rewrite et1. rewrite div_Even.
      destruct (Even_or_Odd t1) as [[t2 et2] | [t2 et2]]; arithmetize.
      * rewrite et2. rewrite div_Even.
        destruct (Even_or_Odd t2) as [[t3 et3] | [t3 et3]]; arithmetize.
        -- rewrite et3. rewrite div_Even. subst t0 t1 t2. nia.
        -- rewrite et3. rewrite div_Odd. subst t0 t1 t2. nia.
      * rewrite et2. rewrite div_Odd.
        destruct (Even_or_Odd t2) as [[t3 et3] | [t3 et3]]; arithmetize.
        -- rewrite et3. rewrite div_Even. subst t0 t1 t2. nia.
        -- rewrite et3. rewrite div_Odd. subst t0 t1 t2. nia.
    + rewrite et1. rewrite div_Odd.
      destruct (Even_or_Odd t1) as [[t2 et2] | [t2 et2]]; arithmetize.
      * rewrite et2. rewrite div_Even.
        destruct (Even_or_Odd t2) as [[t3 et3] | [t3 et3]]; arithmetize.
        -- rewrite et3. rewrite div_Even. subst t0 t1 t2. nia.
        -- rewrite et3. rewrite div_Odd. subst t0 t1 t2. nia.
      * rewrite et2. rewrite div_Odd.
        destruct (Even_or_Odd t2) as [[t3 et3] | [t3 et3]]; arithmetize.
        -- rewrite et3. rewrite div_Even. subst t0 t1 t2. nia.
        -- rewrite et3. rewrite div_Odd. subst t0 t1 t2. nia.
  - change 8 with (2 * (2 * 2)). repeat rewrite <- (div_div _ 2) by lia.
    rewrite add_sub_assoc by lia.
    remember (t + 2 * s - 1) as t0 eqn : et0.
    destruct (Even_or_Odd t0) as [[t1 et1] | [t1 et1]]; arithmetize.
    + rewrite et1. rewrite div_Even.
      destruct (Even_or_Odd t1) as [[t2 et2] | [t2 et2]]; arithmetize.
      * rewrite et2. rewrite div_Even.
        destruct (Even_or_Odd t2) as [[t3 et3] | [t3 et3]]; arithmetize.
        -- rewrite et3. rewrite div_Even. subst t0 t1 t2. nia.
        -- rewrite et3. rewrite div_Odd. subst t0 t1 t2. nia.
      * rewrite et2. rewrite div_Odd.
        destruct (Even_or_Odd t2) as [[t3 et3] | [t3 et3]]; arithmetize.
        -- rewrite et3. rewrite div_Even. subst t0 t1 t2. nia.
        -- rewrite et3. rewrite div_Odd. subst t0 t1 t2. nia.
    + rewrite et1. rewrite div_Odd.
      destruct (Even_or_Odd t1) as [[t2 et2] | [t2 et2]]; arithmetize.
      * rewrite et2. rewrite div_Even.
        destruct (Even_or_Odd t2) as [[t3 et3] | [t3 et3]]; arithmetize.
        -- rewrite et3. rewrite div_Even. subst t0 t1 t2. nia.
        -- rewrite et3. rewrite div_Odd. subst t0 t1 t2. nia.
      * rewrite et2. rewrite div_Odd.
        destruct (Even_or_Odd t2) as [[t3 et3] | [t3 et3]]; arithmetize.
        -- rewrite et3. rewrite div_Even. subst t0 t1 t2. nia.
        -- rewrite et3. rewrite div_Odd. subst t0 t1 t2. nia.
Qed.

(** The function [untri_rem] truly produces a remainder. *)

Lemma tri_untri_untri_rem (n : N) : n - tri (untri n) <= untri n.
Proof.
  rewrite tri_eqn, untri_eqn.
  remember (1 + 8 * n) as p eqn : ep.
  destruct (Even_or_Odd (sqrt p - 1)) as [[q eq] | [q eq]]; arithmetize.
  - rewrite eq. rewrite div_Even.
    destruct (Even_mul_consecutive q) as [r er].
    rewrite er. rewrite div_Even.
    destruct (sqrt_spec' p) as [l0 l1]; arithmetize. clear l0; nia.
  - rewrite eq. rewrite div_Odd.
    destruct (Even_mul_consecutive q) as [r er].
    rewrite er. rewrite div_Even.
    destruct (sqrt_spec' p) as [l0 l1]; arithmetize. clear l0; nia.
Qed.

(** The function [untri_rem] is an inverse of [tri]. *)

Theorem untri_rem_tri (n : N) : untri_rem (tri n) = (n, 0).
Proof. rewrite untri_rem_tri_untri. rewrite untri_tri. f_equal. lia. Qed.

(** The function [tri] is an inverse of [untri_rem]. *)

Theorem tri_untri_rem (n : N) : prod_uncurry (flip add o tri) (untri_rem n) = n.
Proof.
  rewrite untri_rem_tri_untri.
  cbv [prod_uncurry compose flip fst snd].
  pose proof tri_untri n as l.
  lia.
Qed.

(** The function [untri_error] can be defined in terms of [untri_rem]. *)

Lemma untri_error_untri_rem (n : N) :
  untri_error n =
  let (u, t1) := untri_rem n in
  if t1 =? 0 then Some u else None.
Proof.
  pose proof tri_untri n as l. revert l.
  rewrite untri_error_eqn. rewrite untri_rem_tri_untri.
  rewrite untri_eqn. rewrite tri_eqn.
  rewrite <- sqrtrem_sqrt. cbv [fst snd].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es.
  rewrite <- (div_eucl_div (s - 1) 2). cbv [fst snd].
  destruct_div_eucl q r eqr eq e0qr l1qr.
  clear eqr eq.
  destruct (Even_mul_consecutive q) as [u eu].
  rewrite eu. rewrite div_Even. intros l.
  assert (or' : r = 0 \/ r = 1) by lia. clear l1qr.
  destruct (eqb_spec t 0) as [e0 | f0],
  (eqb_spec (n - u) 0) as [e1 | f1]; arithmetize.
  + auto.
  + exfalso. clear l; nia.
  + exfalso. clear l; nia.
  + auto.
Qed.

(** The function [untri_error] is a lifted inverse of [tri]. *)

Theorem untri_error_tri (n : N) : untri_error (tri n) = Some n.
Proof. rewrite untri_error_untri_rem. rewrite untri_rem_tri. auto. Qed.

(** A lifting of the function [tri] is an inverse of [untri_error]. *)

Theorem tri_untri_error (n p : N)
  (e : option_map tri (untri_error n) = Some p) : n = p.
Proof.
  rewrite untri_error_untri_rem in e.
  rewrite untri_rem_tri_untri in e.
  destruct (eqb_spec (n - tri (untri n)) 0) as [e0 | f0].
  - cbv [option_map] in e.
    injection e; intros e1. clear e.
    rewrite <- e1. clear e1.
    pose proof sub_add _ _ (tri_untri n) as e2. lia.
  - cbv [option_map] in e.
    inversion e.
Qed.

(** An inverse of the generating function,
    with a remainder as an exact quotient. *)

Program Definition untri_quotrem (n : N) :
  {x : N * N $ Squash (let (p, q) := x in tri p + q < tri (1 + p))} :=
  Sexists _ (untri_rem n) _.
Next Obligation.
  intros n. cbv beta. apply squash. rewrite untri_rem_tri_untri.
  rewrite tri_succ.
  pose proof tri_untri_untri_rem n as e.
  lia.
Qed.

Global Instance tri_wd : Proper (Logic.eq ==> Logic.eq) tri.
Proof. intros n p e. auto using f_equal. Qed.

Global Instance untri_wd : Proper (Logic.eq ==> Logic.eq) untri.
Proof. intros n p e. auto using f_equal. Qed.

Global Instance le_tri_wd : Proper (N.le ==> N.le) tri.
Proof. intros n p l. apply tri_le_mono. lia. Qed.

Global Instance le_untri_wd : Proper (N.le ==> N.le) untri.
Proof. intros n p l. apply untri_le_mono. lia. Qed.
