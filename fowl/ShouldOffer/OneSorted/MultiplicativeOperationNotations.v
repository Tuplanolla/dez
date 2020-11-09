From Maniunfold.Offers Require Export
  OneSorted.PositiveOperations OneSorted.NaturalOperations
  OneSorted.IntegerOperations.
From Maniunfold.ShouldHave Require Export
  OneSorted.MultiplicativeNotations.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "x '^' n" (at level 30, right associativity).

Reserved Notation "'_^_'" (at level 0, no associativity).

Notation "x '^' n" := (positive_op bin_op n x) : positive_scope.
Notation "'_^_'" := (flip (positive_op bin_op))
  (only parsing) : positive_scope.
Notation "x '^' n" := (nat_op bin_op null_op n x) : nat_scope.
Notation "'_^_'" := (flip (nat_op bin_op null_op)) (only parsing) : nat_scope.
Notation "x '^' n" := (n_op bin_op null_op n x) : N_scope.
Notation "'_^_'" := (flip (n_op bin_op null_op)) (only parsing) : N_scope.
Notation "x '^' n" := (z_op bin_op null_op un_op n x) : Z_scope.
Notation "'_^_'" := (flip (z_op bin_op null_op un_op))
  (only parsing) : Z_scope.
