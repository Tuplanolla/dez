From Coq Require Import NArith List Decimal Ascii String.

Import ListNotations.

Fixpoint string_of_uint (n : uint) : string :=
  match n with
  | Nil => ""%string
  | D0 p => String "0"%char (string_of_uint p)
  | D1 p => String "1"%char (string_of_uint p)
  | D2 p => String "2"%char (string_of_uint p)
  | D3 p => String "3"%char (string_of_uint p)
  | D4 p => String "4"%char (string_of_uint p)
  | D5 p => String "5"%char (string_of_uint p)
  | D6 p => String "6"%char (string_of_uint p)
  | D7 p => String "7"%char (string_of_uint p)
  | D8 p => String "8"%char (string_of_uint p)
  | D9 p => String "9"%char (string_of_uint p)
  end.

Section Natural.

Import N.

Open Scope N_scope.

Fixpoint N_compute (ns : list N) : N :=
  match ns with
  | [] => 0
  | p :: ps => p + N_compute ps
  end.

Definition string_of_N (n : N) : string :=
  string_of_uint (to_uint n).

Fixpoint N_format (ns : list N) : string :=
  match ns with
  | [] => ""
  | [p] => string_of_N p
  | p :: ps => "(" ++ string_of_N p ++ " + " ++ N_format ps ++ ")"
  end.

End Natural.

(** Add powers of two. *)

Section Positive.

Import Pos.

Open Scope positive_scope.

Reserved Notation "'double'" (at level 0, no associativity).
Notation "'double'" := xO (only parsing) : positive_scope.

Fixpoint positive_powers_of_two (n : positive) : list positive :=
  match n with
  | p ~ 1 => 1 :: map double (positive_powers_of_two p)
  | p ~ 0 => map double (positive_powers_of_two p)
  | 1 => [1]
  end.

End Positive.

Section Natural.

Import N.

Open Scope N_scope.
Open Scope string_scope.

Definition N_powers_of_two (n : N) : list N :=
  match n with
  | 0 => []
  | pos p => map pos (positive_powers_of_two p)
  end.

Compute map (fun n : N => N_format (N_powers_of_two n))
  (map of_nat (seq 0 16)).

Lemma N_compute_map_double : forall ns : list N,
  N_compute (map double ns) = double (N_compute ns).
Proof.
  intros ns. induction ns as [| p ps IH].
  - reflexivity.
  - cbn. rewrite IH. rewrite double_add. reflexivity. Qed.

Theorem N_powers_of_two_valid : forall n : N,
  N_compute (N_powers_of_two n) = n.
Proof.
  intros n. destruct n as [| p].
  - reflexivity.
  - cbv [N_powers_of_two]. induction p as [q IH | q IH |].
    + cbn. rewrite map_map.
      replace (fun x : positive => pos x ~ 0) with
        (fun x : positive => N.double (pos x)) by reflexivity.
      rewrite <- map_map. rewrite N_compute_map_double.
      rewrite IH. reflexivity.
    + cbn. rewrite map_map.
      replace (fun x : positive => pos x ~ 0) with
        (fun x : positive => N.double (pos x)) by reflexivity.
      rewrite <- map_map. rewrite N_compute_map_double.
      rewrite IH. reflexivity.
    + reflexivity. Qed.

End Natural.

(** Add a power of two and a residue. *)

Section Positive.

Import Pos.

Open Scope positive_scope.

Reserved Notation "x '/' '2'" (at level 40, left associativity).
Notation "x '/' '2'" := (Pos.div2 x) : positive_scope.

Definition positive_power_and_residue (n : positive) : list positive :=
  if n =? 1 then [1] else let p : positive := size n - 1 in
  if n =? 2 ^ p then [n / 2; n / 2] else [n - 2 ^ p; 2 ^ p].

End Positive.

Section Natural.

Import N.

Open Scope N_scope.
Open Scope string_scope.

Definition N_power_and_residue (n : N) : list N :=
  match n with
  | 0 => []
  | pos p => map pos (positive_power_and_residue p)
  end.

Compute map (fun n : N => N_format (N_power_and_residue n))
  (map of_nat (seq 0 16)).

Theorem N_power_and_residue_valid : forall n : N,
  N_compute (N_power_and_residue n) = n.
Proof.
  intros n. destruct n as [| p].
  - reflexivity.
  - cbv [N_power_and_residue positive_power_and_residue].
    destruct (Pos.eqb_spec p 1)%positive as [H | H].
    + rewrite H. reflexivity.
    + destruct (Pos.eqb_spec p (2 ^ (Pos.size p - 1)))%positive as [H' | H'].
      * cbn. f_equal. destruct p as [q | q |]. all: cbn in *.
        -- admit.
        -- rewrite Pos.add_diag. reflexivity.
        -- exfalso. apply H. reflexivity.
      * cbn. f_equal. destruct p as [q | q |]. all: cbn in *.
        -- admit.
        -- admit.
        -- exfalso. apply H. reflexivity. Admitted.

End Natural.
