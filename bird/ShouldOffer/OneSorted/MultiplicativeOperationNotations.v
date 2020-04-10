From Maniunfold.Offers Require Export
  OneSorted.PositiveOperations OneSorted.NaturalOperations
  OneSorted.IntegerOperations.
From Maniunfold.ShouldHave Require Export
  OneSorted.MultiplicativeNotations.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "x '^' n" (at level 30, right associativity).

Notation "x '^' n" := (positive_op n x) : positive_scope.
Notation "x '^' n" := (nat_op n x) : nat_scope.
Notation "x '^' n" := (n_op n x) : N_scope.
Notation "x '^' n" := (z_op n x) : Z_scope.
