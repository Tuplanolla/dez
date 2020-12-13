From Coq Require Import
  Lia Lists.List NArith.NArith.
From Maniunfold.Provides Require Export
  OptionTheorems ProductTheorems TriangularNumbers.

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
  cbv [prod_uncurry unpair pair]. arithmetize. cbn. Admitted.

Theorem pair_unpair (p q : N) : pair (prod_uncurry unpair (p, q)) = (p, q).
Proof. Admitted.

End Hyperbolic.

(* Fixpoint steps (l : list (N * N)) : list N :=
  match l with
  | [] => []
  | (p, q) :: ((p', q') :: _) as t => if q =? q' then steps t else p :: steps t
  | (p, q) :: t => steps t
  end. *)
