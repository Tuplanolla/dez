From Coq Require Import
  PArith.PArith Program.Wf.
From Maniunfold Require Export
  Init.

From Coq Require Import Lia List Recdef.
Import ListNotations Pos.

Local Open Scope positive_scope.

Definition seq (n p : positive) : list positive :=
  map of_nat (seq (to_nat n) (to_nat p)).

(** A deep dive into "efficient pairing functions".
    Positive domain constraints make them even more horrifying. *)

(** * Cantor (triangle shell) *)

Definition tri (n : positive) : positive :=
  div2 (n * (1 + n)).

Definition tri_inverse_lb (n : positive) : positive :=
  sqrt (2 * n) - 1.

Definition tri_inverse_ub (n : positive) : positive :=
  sqrt (2 * n).

Definition tri_search (n p q : positive) : positive :=
  if q <? tri p then n else p.

Definition tri_inverse (n : positive) : positive :=
  tri_search (tri_inverse_lb n) (tri_inverse_ub n) n.

Definition c_unpair (n p : positive) : positive :=
  div2 (3 + (n + p - 1) ^ 2 - n - p) + p - 1.
  (* div2 (4 + (n + p) ^ 2 - 3 * (n + p)) + p - 1. *)

Definition c_pair (n : positive) : positive * positive :=
  match peanoView n with
  | PeanoOne => (1, 1)
  | PeanoSucc p _ =>
  let q := tri_inverse p in
  let r := n - tri q in
  (2 + q - r, r)
  end.

(* Compute map (prod_uncurry c_unpair o c_pair) (map of_nat (seq 1%nat 64%nat)). *)

(** * Szudzik (square shell) *)


Definition s_unpair (n p : positive) : positive :=
  if p <? n then
  1 + n * n + p - 2 * n else
  p * p + n + p - 2 * p.

Definition s_pair (n : positive) : positive * positive :=
  match peanoView n with
  | PeanoOne => (1, 1)
  | PeanoSucc p _ =>
    let q := sqrt p in
    let r := q * q in
    let s := 1 + q in
    if n <? s + r then
    (s, n - r) else
    (n - r - q, s)
  end.

(** * Rosenberg--Strong (square shell) *)

Definition rs_unpair (n p : positive) : positive :=
  let q := max n p in
  (** We now know [n <= q] and [p <= q], so [n < 1 + q].
      Therefore [1 + n < 1 + 1 + q], leading to
      [1 < 1 + 1 + q - n] and thus [1 <= 1 + q - n].
      Similarly [1 <= 1 + q - p].
      This is probably useless information. *)
  let r := q * q in
  (** We now know [q <= r], so [q < 1 + r].
      Therefore [1 + q < 1 + 1 + r], leading to
      [1 < 1 + 1 + r - q] and thus [1 <= 1 + r - q].
      This is the tightest we can cut it. *)
  1 + r - q + p - n.

Definition rs_pair (n : positive) : positive * positive :=
  match peanoView n with
  | PeanoOne => (1, 1)
  | PeanoSucc p _ =>
    let q := sqrt p in
    let r := q * q in
    let s := 1 + q in
    if n <? s + r then
    (s, n - r) else
    (2 * s + r - n, s)
  end.

(* Compute map (prod_uncurry rs_unpair o rs_pair)
  (map of_nat (seq (S O) 64%nat)). *)
