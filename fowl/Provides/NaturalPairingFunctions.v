From Coq Require Import
  Lia Lists.List NArith.NArith.
From Maniunfold.Provides Require Export
  OptionTheorems.

Import ListNotations N.

Local Open Scope N_scope.

Local Opaque "+" "*" "^" "-" "/" sqrt.

Local Definition seq (n p : N) : list N :=
  map of_nat (seq (to_nat n) (to_nat p)).

(** Triangular number generator. *)

Definition tri (n : N) : N :=
  n * (1 + n) / 2.

Arguments tri _ : assert.

(** Inverse of the triangular number generator, with remainder. *)

Definition untri_rem (n : N) : N * N :=
  let ((* square root *) s, (* remainder *) r) := sqrtrem (1 + 8 * n) in
  let ((* quotient *) q, (* remainder *) r') := div_eucl (s - 1) 2 in
  (q, r + r'). (* wrong *)

Compute map (untri_rem o tri) (seq 0 32).
Compute map untri_rem (seq 0 32).
Compute map ((fun '(p, r) => tri p + r) o untri_rem) (seq 0 32).

Theorem untri_rem_tri (n : N) : snd (untri_rem (tri n)) = 0.
Proof. Admitted.

Theorem tri_untri_rem (n : N) : (fun '(p, r) => tri p + r) (untri_rem n) = n.
Proof. Admitted.

(** Inverse of the triangular number generator, rounding down. *)

Definition untri_down (n : N) : N :=
  (sqrt (1 + 8 * n) - 1) / 2.

Arguments untri_down _ : assert.

Theorem untri_down_tri (n : N) : untri_down (tri n) = n.
Proof.
  induction n as [| p eip] using peano_ind.
  - auto.
  - cbv [untri_down tri] in *.
    rewrite add_succ_r. rewrite mul_succ_r. rewrite add_succ_r.
    rewrite mul_succ_l. rewrite <- divide_div_mul_exact.
    rewrite (mul_comm 8). rewrite divide_div_mul_exact.
    replace (8 / 2) with 4 by admit.
    rewrite mul_succ_l. admit. Admitted.

Theorem tri_untri_down (n : N) : tri (untri_down n) <= n.
Proof. Admitted.

(** Inverse of the triangular number generator, partial. *)

Definition untri (n : N) : option N :=
  let (* radicand *) r := 1 + 8 * n in
  let (* root *) t := sqrt r in
  if r =? t ^ 2 then Some ((t - 1) / 2) else None.

Arguments untri _ : assert.

Lemma tri_untri_succ (n : N) :
  option_map tri (untri (succ n)) = option_map (succ o tri) (untri n).
Proof. Admitted.

Theorem untri_tri (n : N) : untri (tri n) = Some n.
Proof.
  induction n as [| p eip] using peano_ind.
  - auto.
  - cbv [untri tri] in *.
    match goal with
    | |- context [?x =? ?y] => destruct (eqb_spec x y) as [esp | fsp]
    end;
    match goal with
    | _ : context [?x =? ?y] |- _ => destruct (eqb_spec x y) as [ep | fp]
    end.
    + injection eip; clear eip; intros eip.
      f_equal. admit.
    + inversion eip.
    + injection eip; clear eip; intros eip.
      exfalso. apply fsp; clear fsp. admit.
    + inversion eip. Admitted.

Theorem tri_untri (n p : N) (e : option_map tri (untri n) = Some p) :
  n = p.
Proof.
  generalize dependent p.
  induction n as [| i ei] using peano_ind; intros p enp.
  - cbn in enp. injection enp. auto.
  - rewrite tri_untri_succ in enp. rewrite option_map_compose in enp.
    rewrite (ei (pred p)).
    try match goal with
    | _ : context [?x =? ?y] |- _ => destruct (eqb_spec x y) as [e | f]
    end.
    cbv [option_map] in enp. destruct (untri i) eqn : e.
    + injection enp; clear enp; intros enp. rewrite <- enp at 2. admit.
    + inversion enp. Admitted.

(* Compute map untri (seq 0 32).
Compute map tri (seq 0 32).
Compute map (untri o tri) (seq 0 32).
Compute map (option_map tri o untri) (seq 0 32).
Compute (filter is_Some o map (option_map tri o untri)) (seq 0 32). *)

Module Cantor.

Module Nonalternating.

Definition pair (n : N) : N * N :=
  let p := untri_down n in
  let q := n - tri p in
  (p - q, q).

Arguments pair _ : assert.

Definition unpair (n p : N) : N :=
  let q := n + p in
  q * (1 + q) / 2 + p.

Arguments unpair _ _ : assert.

(* Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64). *)

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. cbv [prod_uncurry unpair pair]. cbn.  Admitted.

Theorem pair_unpair (n p : N) : pair (prod_uncurry unpair (n, p)) = (n, p).
Proof. Admitted.

End Nonalternating.

Module Alternating.

Definition pair (n : N) : N * N :=
  let p := untri_down n in
  let q := n - tri p in
  if even p then
  (p - q, q) else
  (q, p - q).

Arguments pair _ : assert.

Definition unpair (n p : N) : N :=
  let q := n + p in
  if even q then
  div2 (q * (1 + q)) + p else
  div2 (q * (1 + q)) + n.

Arguments unpair _ _ : assert.

(* Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64). *)

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (n p : N) : pair (prod_uncurry unpair (n, p)) = (n, p).
Proof. Admitted.

End Alternating.

End Cantor.

Module Szudzik.

Module Nonalternating.

Definition pair (n : N) : N * N :=
  let q := sqrt n in
  let r := q * q in
  if n <? q + r then
  (q, n - r) else
  (n - r - q, q).

Arguments pair _ : assert.

Definition unpair (n p : N) : N :=
  if p <? n then
  n * n + p else
  p * p + n + p.

Arguments unpair _ _ : assert.

(* Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64). *)

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (n p : N) : pair (prod_uncurry unpair (n, p)) = (n, p).
Proof. Admitted.

End Nonalternating.

Module Alternating.

Definition pair (n : N) : N * N :=
  let q := sqrt n in
  let r := q * q in
  if even q then
  if n <? q + r then
  (q, n - r) else
  (n - r - q, q) else
  if n <? q + r then
  (n - r, q) else
  (q, n - r - q).

Arguments pair _ : assert.

Definition unpair (n p : N) : N :=
  let q := max n p in
  if even q then
  if p <? n then
  n * n + p else
  p * p + n + p else
  if n <? p then
  p * p + n else
  n * n + p + n.

Arguments unpair _ _ : assert.

(* Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64). *)

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (n p : N) : pair (prod_uncurry unpair (n, p)) = (n, p).
Proof. Admitted.

End Alternating.

End Szudzik.

Module RosenbergStrong.

Module Nonalternating.

Definition pair (n : N) : N * N :=
  let q := sqrt n in
  if n <? q * q + q then (q, n - q * q) else (q * q + 2 * q - n, q).

Arguments pair _ : assert.

Definition unpair (n p : N) : N :=
  let q := max n p in
  q * q + q + p - n.

Arguments unpair _ _ : assert.

(* Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64). *)

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (n p : N) : pair (prod_uncurry unpair (n, p)) = (n, p).
Proof. Admitted.

End Nonalternating.

Module Alternating.

Definition pair (n : N) : N * N :=
  let q := sqrt n in
  if even q then
  if n <? q * q + q then (q, n - q * q) else (q * q + 2 * q - n, q) else
  if n <? q * q + q then (n - q * q, q) else (q, q * q + 2 * q - n).

Arguments pair _ : assert.

Definition unpair (n p : N) : N :=
  let q := max n p in
  if even q then
  q * q + q + p - n else
  q * q + q + n - p.

Arguments unpair _ _ : assert.

(* Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64). *)

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (n p : N) : pair (prod_uncurry unpair (n, p)) = (n, p).
Proof. Admitted.

End Alternating.

End RosenbergStrong.
