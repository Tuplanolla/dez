From Coq Require Import Ascii Decimal List NArith String.

Module StringNotations.

Notation "x '::' xs" := (String x xs) : string_scope.
Notation "'[' ']'" := EmptyString : string_scope.
Notation "'[' x ']'" := (String x EmptyString) : string_scope.
Notation "'[' x ';' y ';' .. ';' z ']'" :=
  (String x (String y .. (String z EmptyString) ..)) : string_scope.

End StringNotations.

Import StringNotations.

Fixpoint string_of_uint (n : uint) : string :=
  match n with
  | Nil => ""
  | D0 p => "0" :: string_of_uint p
  | D1 p => "1" :: string_of_uint p
  | D2 p => "2" :: string_of_uint p
  | D3 p => "3" :: string_of_uint p
  | D4 p => "4" :: string_of_uint p
  | D5 p => "5" :: string_of_uint p
  | D6 p => "6" :: string_of_uint p
  | D7 p => "7" :: string_of_uint p
  | D8 p => "8" :: string_of_uint p
  | D9 p => "9" :: string_of_uint p
  end.

Section Natural.

Import ListNotations N.

Definition string_of_N (n : N) : string :=
  string_of_uint (to_uint n).

Open Scope N_scope.

Fixpoint N_compute (ns : list N) : N :=
  match ns with
  | [] => 0
  | p :: ps => p + N_compute ps
  end.

Fixpoint N_format (ns : list N) : string :=
  match ns with
  | [] => ""
  | [p] => string_of_N p
  | p :: ps => "(" ++ string_of_N p ++ " + " ++ N_format ps ++ ")"
  end.

End Natural.

(** Add powers of two. *)

Section Positive.

Import ListNotations Pos.

Open Scope positive_scope.

Fixpoint positive_powers_of_two (n : positive) : list positive :=
  match n with
  | p ~ 1 => 1 :: map xO (positive_powers_of_two p)
  | p ~ 0 => map xO (positive_powers_of_two p)
  | 1 => [1]
  end.

End Positive.

Section Natural.

Import ListNotations N.

Open Scope string_scope.
Open Scope list_scope.
Open Scope N_scope.

Definition N_powers_of_two (n : N) : list N :=
  match n with
  | 0 => []
  | pos p => map pos (positive_powers_of_two p)
  end.

Compute map (fun n : N => N_compute (N_powers_of_two n))
  (map of_nat (seq 0 16)).

Compute map (fun n : N => N_format (N_powers_of_two n))
  (map of_nat (seq 0 16)).

Lemma N_compute_map_double : forall ns : list N,
  N_compute (map double ns) = double (N_compute ns).
Proof.
  intros ns. induction ns as [| p ps IH].
  - reflexivity.
  - cbn [map N_compute]. rewrite IH. rewrite double_add. reflexivity. Qed.

Theorem N_powers_of_two_valid : forall n : N,
  N_compute (N_powers_of_two n) = n.
Proof.
  intros n. destruct n as [| p].
  - reflexivity.
  - cbv [N_powers_of_two]. induction p as [q IH | q IH |].
    + cbn [positive_powers_of_two map N_compute]. rewrite map_map.
      replace (fun x : positive => pos x ~ 0) with
        (fun x : positive => double (pos x)) by reflexivity.
      rewrite <- map_map. rewrite N_compute_map_double.
      rewrite IH. reflexivity.
    + cbn [positive_powers_of_two]. rewrite map_map.
      replace (fun x : positive => pos x ~ 0) with
        (fun x : positive => double (pos x)) by reflexivity.
      rewrite <- map_map. rewrite N_compute_map_double.
      rewrite IH. reflexivity.
    + reflexivity. Qed.

End Natural.

(** Add a power of two and its residue. *)

Section Natural.

Import ListNotations N.

Open Scope string_scope.
Open Scope list_scope.
Open Scope N_scope.

Definition N_power_and_residue (n : N) : list N :=
  if n =? 0 then [] else
  if n =? 1 then [1] else
  let p : N := log2 n in
  if n =? 2 ^ p then [n / 2; n / 2] else
  [n - 2 ^ p; 2 ^ p].

Compute map (fun n : N => N_compute (N_power_and_residue n))
  (map of_nat (seq 0 16)).

Compute map (fun n : N => N_format (N_power_and_residue n))
  (map of_nat (seq 0 16)).

Theorem N_power_and_residue_valid : forall n : N,
  N_compute (N_power_and_residue n) = n.
Proof.
  intros n. cbv [N_power_and_residue].
  destruct (eqb_spec n 0) as [H0 | H0].
  - rewrite H0. reflexivity.
  - destruct (eqb_spec n 1) as [H1 | H1].
    + rewrite H1. reflexivity.
    + destruct (eqb_spec n (2 ^ log2 n)) as [H2 | H2].
      * cbv [N_compute]. ring_simplify.
        destruct (log2 n) as [| p _] using peano_ind.
        -- exfalso. apply H1. apply H2.
        -- pose proof (neq_succ_0 1) as H.
          symmetry. rewrite (div_exact n 2 H). rewrite (mod_divides n 2 H).
          exists (2 ^ p). rewrite <- pow_succ_r'. apply H2.
      * cbv [N_compute]. ring_simplify.
        rewrite (sub_add (2 ^ log2 n) n).
        -- reflexivity.
        -- apply log2_spec. rewrite <- (neq_0_lt_0 n). apply H0. Qed.

End Natural.
