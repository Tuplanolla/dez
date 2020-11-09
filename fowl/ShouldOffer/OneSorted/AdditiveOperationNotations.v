From Maniunfold.Offers Require Export
  OneSorted.PositiveOperations OneSorted.NaturalOperations
  OneSorted.IntegerOperations.
From Maniunfold.ShouldHave Require Export
  OneSorted.AdditiveNotations.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "n '*' x" (at level 40, left associativity).

Reserved Notation "'_*_'" (at level 0, no associativity).

Notation "n '*' x" := (positive_op bin_op n x) : positive_scope.
Notation "'_*_'" := (positive_op bin_op) (only parsing) : positive_scope.
Notation "n '*' x" := (nat_op bin_op null_op n x) : nat_scope.
Notation "'_*_'" := (nat_op bin_op null_op) (only parsing) : nat_scope.
Notation "n '*' x" := (n_op bin_op null_op n x) : N_scope.
Notation "'_*_'" := (n_op bin_op null_op) (only parsing) : N_scope.
Notation "n '*' x" := (z_op bin_op null_op un_op n x) : Z_scope.
Notation "'_*_'" := (z_op bin_op null_op un_op) (only parsing) : Z_scope.
