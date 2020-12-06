From Coq Require Import
  Lia Lists.List NArith.NArith.
From Maniunfold.Provides Require Export
  OptionTheorems.

Import ListNotations N.

Local Open Scope N_scope.

Local Opaque "+" "*" "^" "-" "/" sqrt.

Local Definition seq (n p : N) : list N :=
  map of_nat (seq (to_nat n) (to_nat p)).

(** Triangular number function. *)

Definition tri (n : N) : N :=
  (* n * (1 + n) / 2 *)
  shiftr (n * succ n) 1.

Arguments tri _ : assert.

(** Inverse of the triangular number function, rounding down. *)

Definition untri (n : N) : N :=
  (* (sqrt (1 + 8 * n) - 1) / 2 *)
  shiftr (pred (sqrt (succ (shiftl n 3)))) 1.

Arguments untri _ : assert.

Theorem untri_tri (n : N) : untri (tri n) = n.
Proof.
  induction n as [| p eip] using peano_ind.
  - auto.
  - cbv [untri tri] in *. Admitted.

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

(** Inverse of the triangular number function, with remainder. *)

Definition untri_rem (n : N) : N * N :=
  (* let (* quotient *) q := (sqrt (1 + 8 * n) - 1) / 2 in
  (q, n - tri q) *)
  let q := shiftr (pred (sqrt (succ (shiftl n 3)))) 1 in
  (q, n - tri q).

Compute map (prod_uncurry (add o tri) o untri_rem) (seq 0 32).
Compute map untri_rem (seq 0 32).
Compute map (untri_rem o tri) (seq 0 32).

Theorem untri_rem_tri (n : N) : snd (untri_rem (tri n)) = 0.
Proof. Admitted.

Theorem tri_untri_rem (n : N) : prod_uncurry (add o tri) (untri_rem n) = n.
Proof. Admitted.

Module Cantor.

Module Nonalternating.

Definition pair_shell (n : N) : N :=
  untri n.

Arguments pair_shell _ : assert.

Definition pair (n : N) : N * N :=
  let ((* shell *) s, (* index *) i) := untri_rem n in
  (s - i, i).

Arguments pair _ : assert.

Definition unpair_shell (n p : N) : N :=
  n + p.

Arguments unpair_shell _ _ : assert.

Definition unpair (n p : N) : N :=
  let (* shell *) s := n + p in
  s * (1 + s) / 2 + p.

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Compute map pair_shell (seq 0 64).
Compute map (prod_uncurry unpair_shell o pair) (seq 0 64).

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof. cbv [prod_uncurry unpair pair]. cbn. Admitted.

Theorem pair_unpair (n p : N) : pair (prod_uncurry unpair (n, p)) = (n, p).
Proof. Admitted.

End Nonalternating.

Module Alternating.

Definition pair (n : N) : N * N :=
  let p := untri n in
  let q := n - tri p in
  if even p then
  (p - q, q) else
  (q, p - q).

Arguments pair _ : assert.

Definition unpair (n p : N) : N :=
  let q := n + p in
  if even q then
  shiftr (q * (1 + q)) 1 + p else
  shiftr (q * (1 + q)) 1 + n.

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

Definition pair_shell (n : N) : N :=
  sqrt n.

Arguments pair_shell _ : assert.

Definition pair (n : N) : N * N :=
  let (* shell *) s := sqrt n in
  let (* starting point *) t := s ^ 2 in
  let (* midpoint *) m := t + s in
  let (* remainder *) r := n - t in
  if n <? m then
  (s, r) else
  (r - s, s).

Arguments pair _ : assert.

Definition unpair_shell (n p : N) : N :=
  max n p.

Arguments unpair_shell _ _ : assert.

Definition unpair (n p : N) : N :=
  let (* shell *) s := max n p in
  let (* starting point *) t := s ^ 2 in
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

Definition pair_shell (n : N) : N :=
  sqrt n.

Arguments pair_shell _ : assert.

Definition pair (n : N) : N * N :=
  let (* shell *) s := sqrt n in
  let (* starting point *) t := s ^ 2 in
  let (* midpoint *) m := t + s in
  if n <? m then
  (s, n - t) else
  (m + s - n, s).

Arguments pair _ : assert.

Definition unpair_shell (n p : N) : N :=
  max n p.

Arguments unpair_shell _ _ : assert.

Definition unpair (n p : N) : N :=
  let (* shell *) s := max n p in
  let (* starting point *) t := s ^ 2 in
  t + s + p - n.

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Compute map pair_shell (seq 0 64).
Compute map (prod_uncurry unpair_shell o pair) (seq 0 64).

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

Module Hyperbolic.

(** Yes, but does it have a name? *)

Module Nonalternating.

Fixpoint A029837 (n : positive) : N :=
  match n with
  | xI p => succ (A029837 p)
  | xO p => succ (A029837 p)
  | xH => 0
  end.

Definition pair_shell (n : N) : N :=
  (* ceil (log2 (1 + n)) *)
  A029837 (succ_pos n).

Arguments pair_shell _ : assert.

Fixpoint A000265 (n : positive) : N :=
  match n with
  | xI p => Npos n
  | xO p => A000265 p
  | xH => Npos n
  end.

Fixpoint A007814 (n : positive) : N :=
  match n with
  | xI p => 0
  | xO p => succ (A007814 p)
  | xH => 0
  end.

Definition pair (n : N) : N * N :=
  (* (A007814 (1 + n), (A000265 (1 + n) - 1) / 2) *)
  (A007814 (succ_pos n), shiftr (pred (A000265 (succ_pos n))) 1).

Arguments pair _ : assert.

Definition unpair_shell (n p : N) : N :=
  (* n + ceil (log2 (1 + 2 * n)) *)
  n + A029837 (succ_pos (shiftl p 1)).

Arguments unpair_shell _ _ : assert.

Definition unpair (n p : N) : N :=
  (* 2 ^ n * (2 * p + 1) - 1 *)
  pred (shiftl 1 n * (succ (shiftl p 1))).

Arguments unpair _ _ : assert.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Compute map pair_shell (seq 0 64).
Compute map (prod_uncurry unpair_shell o pair) (seq 0 64).

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

End Hyperbolic.
