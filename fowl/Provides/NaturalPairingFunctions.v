From Coq Require Import
  Lia Lists.List NArith.NArith.
From Maniunfold Require Export
  Init.

Import ListNotations N.

Local Open Scope N_scope.

Local Definition seq (n p : N) : list N :=
  map of_nat (seq (to_nat n) (to_nat p)).

(** Triangular numbers. *)

Definition tri (n : N) : N :=
  n * (1 + n) / 2.

Definition tri_lb (n : N) : N :=
  n ^ 2 / 2.

Definition tri_ub (n : N) : N :=
  (1 + n) ^ 2 / 2.

Lemma tri_bounded (n : N) : tri_lb n <= tri n <= tri_ub n.
Proof. cbv [tri tri_lb tri_ub]. split.
  - rewrite pow_2_r. apply div_le_mono; lia.
  - rewrite pow_2_r. apply div_le_mono; lia. Qed.

Definition tri_inverse_lb (n : N) : N :=
  sqrt (2 * n) - 1.

Definition tri_inverse_ub (n : N) : N :=
  sqrt (2 * n).

Definition tri_search (n p q : N) : N :=
  if q <? tri p then n else p.

Definition tri_inverse (n : N) : N :=
  tri_search (tri_inverse_lb n) (tri_inverse_ub n) n.

Definition tri_inverse' (n : N) : N :=
  (sqrt (1 + 8 * n) - 1) / 2.

Compute map tri_inverse_lb (seq 0 32).
Compute map tri_inverse_ub (seq 0 32).
Compute map tri_inverse (seq 0 32).
Compute map tri_inverse' (seq 0 32).
Compute map tri (seq 0 32).
Compute map (tri_inverse o tri) (seq 0 32).

(** Nonalternating Cantor pairing function. *)

Definition c_pair (n : N) : N * N :=
  let p := tri_inverse n in
  let q := n - tri p in
  (p - q, q).

Definition c_unpair (n p : N) : N :=
  let q := n + p in
  div2 (q * (1 + q)) + p.

Compute map c_pair (seq 0 64).
Compute map (prod_uncurry c_unpair o c_pair) (seq 0 64).

Definition ca_unpair (n p : N) : N :=
  let q := n + p in
  if even q then
  div2 (q * (1 + q)) + p else
  div2 (q * (1 + q)) + n.

Definition ca_pair (n : N) : N * N :=
  let p := tri_inverse n in
  let q := n - tri p in
  if even p then
  (p - q, q) else
  (q, p - q).

Compute map ca_pair (seq 0 64).
Compute map (prod_uncurry ca_unpair o ca_pair) (seq 0 64).

(** * Szudzik (square shell) *)

Definition s_unpair (n p : N) : N :=
  if p <? n then
  n * n + p else
  p * p + n + p.

Definition s_pair (n : N) : N * N :=
  let q := sqrt n in
  let r := q * q in
  if n <? q + r then
  (q, n - r) else
  (n - r - q, q).

(* Compute map (prod_uncurry s_unpair o s_pair) (seq 0 64). *)

Definition sa_unpair (n p : N) : N :=
  let q := max n p in
  if even q then
  if p <? n then
  n * n + p else
  p * p + n + p else
  if n <? p then
  p * p + n else
  n * n + p + n.

Definition sa_pair (n : N) : N * N :=
  let q := sqrt n in
  let r := q * q in
  if even q then
  if n <? q + r then
  (q, n - r) else
  (n - r - q, q) else
  if n <? q + r then
  (n - r, q) else
  (q, n - r - q).

Compute map sa_pair (seq 0 64).
Compute map (prod_uncurry sa_unpair o sa_pair) (seq 0 64).

(** * Rosenberg--Strong (square shell) *)

Definition rs_unpair (n p : N) : N :=
  let q := max n p in
  q * q + q + p - n.

Definition rs_pair (n : N) : N * N :=
  let q := sqrt n in
  if n <? q * q + q then (q, n - q * q) else (q * q + 2 * q - n, q).

(* Compute map (prod_uncurry rs_unpair o rs_pair) (seq 0 64). *)

Definition rsa_unpair (n p : N) : N :=
  let q := max n p in
  if even q then
  q * q + q + p - n else
  q * q + q + n - p.

Definition rsa_pair (n : N) : N * N :=
  let q := sqrt n in
  if even q then
  if n <? q * q + q then (q, n - q * q) else (q * q + 2 * q - n, q) else
  if n <? q * q + q then (n - q * q, q) else (q, q * q + 2 * q - n).

Compute map rsa_pair (seq 0 64).
Compute map (prod_uncurry rsa_unpair o rsa_pair) (seq 0 64).
