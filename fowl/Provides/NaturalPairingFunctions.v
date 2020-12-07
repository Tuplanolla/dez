From Coq Require Import
  Lia Lists.List NArith.NArith.
From Maniunfold.Provides Require Export
  OptionTheorems ProductTheorems.

Import ListNotations N.

Local Open Scope N_scope.

Local Opaque "+" "*" "^" "-" "/" sqrt.

(** Binary logarithm, rounding down, A000523. *)

Fixpoint log2_down (n : positive) : N :=
  match n with
  | xI p => succ (log2_down p)
  | xO p => succ (log2_down p)
  | xH => 0
  end.

(** Binary logarithm, rounding up, A029837. *)

Definition log2_up (n : positive) : N :=
  match peanoView n with
  | PeanoOne => 0
  | PeanoSucc p _ => succ (log2_down p)
  end.

(** Largest odd number to divide the given number, A000265. *)

Fixpoint odd_part (n : positive) : N :=
  match n with
  | xI p => Npos n
  | xO p => odd_part p
  | xH => Npos n
  end.

(** Largest power of two to divide the given number, A007814.
    Returns the power itself. *)

Fixpoint pow2_part (n : positive) : N :=
  match n with
  | xI p => 0
  | xO p => succ (pow2_part p)
  | xH => 0
  end.

Lemma odd_part_pow2_part (n : positive) :
  odd_part n = Npos n / 2 ^ pow2_part n.
Proof. Admitted.

(** Analogous to [div_eucl] and [sqrtrem]
    in the sense of "maximum with remainder". *)

Local Definition minmax (n p : N) : N * N :=
  prod_sort_by leb (n, p).

Local Lemma minmax_spec (n p : N) :
  let (q, r) := minmax n p in
  n <= p /\ q = n /\ r = p \/
  p <= n /\ q = p /\ r = n.
Proof. cbv [minmax prod_sort_by]. destruct (leb_spec n p); lia. Qed.

Local Definition seq (n p : N) : list N :=
  map of_nat (seq (to_nat n) (to_nat p)).

(** Triangular number function A000217. *)

Definition tri (n : N) : N :=
  (* n * (1 + n) / 2 *)
  shiftr (n * succ n) 1.

Arguments tri _ : assert.

(** Inverse of the triangular number function, rounding down, A003056. *)

Definition untri (n : N) : N :=
  (* (sqrt (1 + 8 * n) - 1) / 2 *)
  shiftr (pred (sqrt (succ (shiftl n 3)))) 1.

Arguments untri _ : assert.

Ltac arithmetize :=
  repeat rewrite <- div2_spec;
  repeat rewrite div2_div;
  repeat rewrite shiftl_mul_pow2;
  repeat rewrite <- add_1_l;
  repeat rewrite <- sub_1_r.

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

Theorem tri_untri_error (n p : N)
  (e : option_map tri (untri_error n) = Some p) :
  n = p.
Proof.
  generalize dependent p.
  induction n as [| i ei] using peano_ind; intros p enp.
  - cbn in enp. injection enp. auto.
  - rewrite tri_untri_error_succ in enp. rewrite option_map_compose in enp.
    rewrite (ei (pred p)).
    try match goal with
    | _ : context [?x =? ?y] |- _ => destruct (eqb_spec x y) as [e | f]
    end.
    cbv [option_map] in enp. destruct (untri_error i) eqn : e.
    + injection enp; clear enp; intros enp. rewrite <- enp at 2. admit.
    + inversion enp. Admitted.

(* Compute map untri (seq 0 32).
Compute map tri (seq 0 32).
Compute map (untri_error o tri) (seq 0 32).
Compute map (option_map tri o untri_error) (seq 0 32).
Compute (filter is_Some o map (option_map tri o untri_error)) (seq 0 32). *)

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

Compute map (prod_uncurry (add o tri) o untri_rem) (seq 0 32).
Compute map untri_rem (seq 0 32).
Compute map (untri_rem o tri) (seq 0 32).

Theorem untri_rem_tri (n : N) : snd (untri_rem (tri n)) = 0.
Proof. Admitted.

Theorem tri_untri_rem (n : N) : prod_uncurry (add o tri) (untri_rem n) = n.
Proof. Admitted.

Module Cantor.

Definition pair_shell (n : N) : N := untri n.

Arguments pair_shell _ : assert.

Definition pair (n : N) : N * N :=
  let ((* shell *) s, (* index in shell *) i) := untri_rem n in
  (s - i, i).

Arguments pair _ : assert.

Definition unpair_shell (p q : N) : N := p + q.

Arguments unpair_shell _ _ : assert.

Definition unpair (p q : N) : N :=
  let (* shell *) s := p + q in
  let (* index in shell *) i := q in
  let (* endpoint *) e := tri s in
  i + e.

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Compute map pair_shell (seq 0 64).
Compute map (prod_uncurry unpair_shell o pair) (seq 0 64).

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. cbv [prod_uncurry unpair pair]. cbn. Admitted.

Theorem pair_unpair (p q : N) : pair (prod_uncurry unpair (p, q)) = (p, q).
Proof. Admitted.

Module Alternating.

Definition pair (n : N) : N * N :=
  let ((* shell *) s, (* index in shell *) i) := untri_rem n in
  let (* continuation *) c := (s - i, i) in
  (if even s then id else prod_swap) c.

Arguments pair _ : assert.

Definition unpair (p q : N) : N :=
  let (* shell *) s := p + q in
  let (* continuation *) c (p q : N) :=
    let (* index in shell *) i := q in
    let (* endpoint *) e := tri s in
    i + e in
  (if even s then id else flip) c p q.

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

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
  let ((* index in leg *) i, (* shell *) s) := minmax p q in
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
  let ((* index in leg *) i, (* shell *) s) := minmax p q in
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
  (s, n - e) else
  (s + m - n, s).

Arguments pair _ : assert.

Definition unpair_shell (p q : N) : N := max p q.

Arguments unpair_shell _ _ : assert.

Definition unpair (p q : N) : N :=
  let ((* index in leg *) i, (* shell *) s) := minmax p q in
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
    (s, n - e) else
    (s + m - n, s) in
  (if even s then id else prod_swap) c.

Arguments pair _ : assert.

Definition unpair (p q : N) : N :=
  let ((* index in leg *) i, (* shell *) s) := minmax p q in
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

Definition pair_shell (n : N) : N :=
  (* log2_down (1 + n) *)
  log2_down (succ_pos n).

Arguments pair_shell _ : assert.

Definition pair (n : N) : N * N :=
  (* (pow2_part (1 + n), (odd_part (1 + n) - 1) / 2) *)
  (pow2_part (succ_pos n), shiftr (pred (odd_part (succ_pos n))) 1).

Arguments pair _ : assert.

Definition unpair_shell (p q : N) : N :=
  (* log2_down (1 + 2 * q) + p *)
  log2_down (succ_pos (shiftl q 1)) + p.

Arguments unpair_shell _ _ : assert.

Definition unpair (p q : N) : N :=
  (* (1 + 2 * q) * 2 ^ p - 1 *)
  pred (succ (shiftl q 1) * shiftl 1 p).

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Compute map pair_shell (seq 0 64).
Compute map (prod_uncurry unpair_shell o pair) (seq 0 64).

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof.
  cbv [prod_uncurry unpair pair]. arithmetize. cbn.
  rewrite mul_1_l. Admitted.

Theorem pair_unpair (p q : N) : pair (prod_uncurry unpair (p, q)) = (p, q).
Proof. Admitted.

End Hyperbolic.
