From Maniunfold.Offers Require Export
  OneSorted.PositiveOperations OneSorted.NaturalOperations
  OneSorted.IntegerOperations.
From Maniunfold.ShouldHave Require Export
  OneSorted.AdditiveNotations.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "n '*' x" (at level 40, left associativity).

Notation "n '*' x" := (positive_op n x) : positive_scope.
Notation "n '*' x" := (nat_op n x) : nat_scope.
Notation "n '*' x" := (n_op n x) : N_scope.
Notation "n '*' x" := (z_op n x) : Z_scope.
