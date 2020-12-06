From Coq Require Import
  Lia Lists.List NArith.NArith.
From Maniunfold.Provides Require Export
  OptionTheorems.

Import ListNotations N.

Local Open Scope N_scope.

Local Opaque "+" "*" "^" "-" "/" sqrt.

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

Lemma tri_succ (n : N) : tri (succ n) = succ n + tri n.
Proof.
  cbv [tri].
  repeat rewrite <- div2_spec.
  repeat rewrite div2_div.
  repeat rewrite <- add_1_l.
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
    cbv [tri untri].
    repeat rewrite shiftl_mul_pow2.
    repeat rewrite <- div2_spec.
    repeat rewrite div2_div.
    repeat rewrite <- add_1_l.
    repeat rewrite <- sub_1_r.
    repeat rewrite <- sqrtrem_sqrt.
    repeat match goal with
    | |- context [sqrtrem ?n] =>
      let x := fresh in pose proof sqrtrem_spec n as x;
      let e := fresh in destruct (sqrtrem n) eqn : e;
      destruct x
    end.
    cbn in *.
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

Definition untri_rem (n : N) : N * N :=
  (* let ((* square root *) s, (* remains *) r) := sqrtrem (1 + 8 * n) in
  let ((* quotient *) q, (* remainder *) e) := div_eucl (s - 1) 2 in
  (q, (r + (2 * s - 1) * e) / 8) *)
  let (s, r) := sqrtrem (succ (shiftl n 3)) in
  let (q, e) := div_eucl (pred s) 2 in
  (q, shiftr (r + pred (shiftl s 1) * e) 3).

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
  let ((* shell *) s, (* index *) i) := untri_rem n in
  (s - i, i).

Arguments pair _ : assert.

Definition unpair_shell (n p : N) : N := n + p.

Arguments unpair_shell _ _ : assert.

Definition unpair (n p : N) : N := tri (unpair_shell n p) + p.

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Compute map pair_shell (seq 0 64).
Compute map (prod_uncurry unpair_shell o pair) (seq 0 64).

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. cbv [prod_uncurry unpair pair]. cbn. Admitted.

Theorem pair_unpair (n p : N) : pair (prod_uncurry unpair (n, p)) = (n, p).
Proof. Admitted.

Module Alternating.

Definition pair (n : N) : N * N :=
  let ((* shell *) s, (* index *) i) := untri_rem n in
  if even s then (s - i, i) else (i, s - i).

Arguments pair _ : assert.

Definition unpair (n p : N) : N :=
  let s := unpair_shell n p in
  tri s + if even s then p else n.

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (n p : N) : pair (prod_uncurry unpair (n, p)) = (n, p).
Proof. Admitted.

End Alternating.

End Cantor.

Module Szudzik.

Definition pair_shell (n : N) : N := sqrt n.

Arguments pair_shell _ : assert.

Definition pair (n : N) : N * N :=
  let (* shell *) s := pair_shell n in
  let (* endpoint *) t := s ^ 2 in
  let (* midpoint *) m := t + s in
  let (* remainder *) r := n - t in
  if n <? m then
  (s, r) else
  (r - s, s).

Arguments pair _ : assert.

Definition unpair_shell (n p : N) : N := max n p.

Arguments unpair_shell _ _ : assert.

Definition unpair (n p : N) : N :=
  let (* shell *) s := unpair_shell n p in
  let (* endpoint *) t := s ^ 2 in
  let (* midpoint *) m := t + n in
  if p <? n then
  t + p else
  m + p.

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Compute map pair_shell (seq 0 64).
Compute map (prod_uncurry unpair_shell o pair) (seq 0 64).

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (n p : N) : pair (prod_uncurry unpair (n, p)) = (n, p).
Proof. Admitted.

Module Alternating.

Definition pair (n : N) : N * N :=
  let (* shell *) s := pair_shell n in
  let (* endpoint *) e := s ^ 2 in
  let (* midpoint *) m := e + s in
  let (* remainder *) r := n - e in
  if n <? m then
  if even s then (s, r) else (r, s) else
  if even s then (r - s, s) else (s, r - s).

Arguments pair _ : assert.

Definition unpair (n p : N) : N :=
  let (* shell *) s := unpair_shell n p in
  let (* endpoint *) e := s ^ 2 in
  if even s then
  let (* midpoint *) m := e + n in
  if p <? n then
  e + p else
  m + p else
  let (* midpoint *) m := e + p in
  if n <? p then
  e + n else
  m + n.

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (n p : N) : pair (prod_uncurry unpair (n, p)) = (n, p).
Proof. Admitted.

End Alternating.

End Szudzik.

Module RosenbergStrong.

Definition pair_shell (n : N) : N := sqrt n.

Arguments pair_shell _ : assert.

(** We could swap to [m - n + s] if [n <= sqrt n ^ 2 + sqrt n], but nope. *)

Definition pair (n : N) : N * N :=
  let (* shell *) s := pair_shell n in
  let (* endpoint *) e := s ^ 2 in
  let (* midpoint *) m := e + s in
  if n <? m then
  (s, n - e) else
  (m + s - n, s).

Arguments pair _ : assert.

Definition unpair_shell (n p : N) : N := max n p.

Arguments unpair_shell _ _ : assert.

(** We first do [s - n], because the lowest it can go is [0]. Optimal! *)

Definition unpair (n p : N) : N :=
  let (* shell *) s := unpair_shell n p in
  let (* endpoint *) e := s ^ 2 in
  let (* remainder *) r := s - n in
  r + e + p.

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Compute map pair_shell (seq 0 64).
Compute map (prod_uncurry unpair_shell o pair) (seq 0 64).

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (n p : N) : pair (prod_uncurry unpair (n, p)) = (n, p).
Proof. Admitted.

Module Alternating.

Definition pair (n : N) : N * N :=
  let (* shell *) s := pair_shell n in
  let (* endpoint *) e := s ^ 2 in
  let (* midpoint *) m := e + s in
  if n <? m then
  if even s then (s, n - e) else (n - e, s) else
  if even s then (m + s - n, s) else (s, m + s - n).

Arguments pair _ : assert.

Definition unpair (n p : N) : N :=
  let (* shell *) s := unpair_shell n p in
  let (* endpoint *) e := s ^ 2 in
  if even s then
  let (* remainder *) r := s - n in
  r + e + p else
  let (* remainder *) r := s - p in
  r + e + n.

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (n p : N) : pair (prod_uncurry unpair (n, p)) = (n, p).
Proof. Admitted.

End Alternating.

End RosenbergStrong.

Module Hyperbolic.

(** Yes, but does it have a name? *)

(** Binary logarithm, rounding up, A029837. *)

Fixpoint log2_up (n : positive) : N :=
  match n with
  | xI p => succ (log2_up p)
  | xO p => succ (log2_up p)
  | xH => 0
  end.

Definition pair_shell (n : N) : N :=
  (* log2_up (1 + n) *)
  log2_up (succ_pos n).

Arguments pair_shell _ : assert.

(** Largest odd number to divide the given number, A000265. *)

Fixpoint oddpart (n : positive) : N :=
  match n with
  | xI p => Npos n
  | xO p => oddpart p
  | xH => Npos n
  end.

(** Largest power of two to divide the given number, A007814. *)

Fixpoint pow2part (n : positive) : N :=
  match n with
  | xI p => 0
  | xO p => succ (pow2part p)
  | xH => 0
  end.

Definition pair (n : N) : N * N :=
  (* (pow2part (1 + n), (oddpart (1 + n) - 1) / 2) *)
  (pow2part (succ_pos n), shiftr (pred (oddpart (succ_pos n))) 1).

Arguments pair _ : assert.

Definition unpair_shell (n p : N) : N :=
  (* n + log2_up (1 + 2 * n) *)
  n + log2_up (succ_pos (shiftl p 1)).

Arguments unpair_shell _ _ : assert.

Definition unpair (n p : N) : N :=
  (* 2 ^ n * (2 * p + 1) - 1 *)
  pred (shiftl 1 n * succ (shiftl p 1)).

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Compute map pair_shell (seq 0 64).
Compute map (prod_uncurry unpair_shell o pair) (seq 0 64).

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. Admitted.

Theorem pair_unpair (n p : N) : pair (prod_uncurry unpair (n, p)) = (n, p).
Proof. Admitted.

End Hyperbolic.
