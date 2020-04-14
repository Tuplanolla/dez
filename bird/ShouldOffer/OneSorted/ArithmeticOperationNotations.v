From Maniunfold.Offers Require Export
  OneSorted.PositiveOperations OneSorted.NaturalOperations
  OneSorted.IntegerOperations.
From Maniunfold.ShouldHave Require Export
  OneSorted.ArithmeticNotations.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "n '*' x" (at level 40, left associativity).
Reserved Notation "x '^' n" (at level 30, right associativity).

Notation "n '*' x" := (positive_op (A_has_bin_op := add) n x) : positive_scope.
Notation "n '*' x" := (nat_op (A_has_bin_op := add)
  (A_has_null_op := zero) n x) : nat_scope.
Notation "n '*' x" := (n_op (A_has_bin_op := add)
  (A_has_null_op := zero) n x) : N_scope.
Notation "n '*' x" := (z_op (A_has_bin_op := add)
  (A_has_null_op := zero) (A_has_un_op := neg) n x) : Z_scope.
Notation "x '^' n" := (positive_op (A_has_bin_op := mul) n x) : positive_scope.
Notation "x '^' n" := (nat_op (A_has_bin_op := mul)
  (A_has_null_op := one) n x) : nat_scope.
Notation "x '^' n" := (n_op (A_has_bin_op := mul)
  (A_has_null_op := one) n x) : N_scope.
Notation "x '^' n" := (z_op (A_has_bin_op := mul)
  (A_has_null_op := one) (A_has_un_op := recip) n x) : Z_scope.
