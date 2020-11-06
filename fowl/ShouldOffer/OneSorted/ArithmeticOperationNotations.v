From Maniunfold.Offers Require Export
  OneSorted.PositiveOperations OneSorted.NaturalOperations
  OneSorted.IntegerOperations.
From Maniunfold.ShouldHave Require Export
  OneSorted.ArithmeticNotations.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "n '*' x" (at level 40, left associativity).
Reserved Notation "x '^' n" (at level 30, right associativity).

Notation "n '*' x" := (positive_op (H := add) n x) : positive_scope.
Notation "n '*' x" := (nat_op (H := add)
  (H0 := zero) n x) : nat_scope.
Notation "n '*' x" := (n_op (H := add)
  (H0 := zero) n x) : N_scope.
Notation "n '*' x" := (z_op (H := add)
  (H0 := zero) (H1 := neg) n x) : Z_scope.
Notation "x '^' n" := (positive_op (H := mul) n x) : positive_scope.
Notation "x '^' n" := (nat_op (H := mul)
  (H0 := one) n x) : nat_scope.
Notation "x '^' n" := (n_op (H := mul)
  (H0 := one) n x) : N_scope.
Notation "x '^' n" := (z_op (H := mul)
  (H0 := one) (H1 := recip) n x) : Z_scope.
