From DEZ.Offers Require Import
  OneSortedNaturalOperations.
From DEZ.ShouldHave Require Export
  OneSortedMultiplicativeNotations.

Notation "x '^' n" := (nat_op null_op bin_op n x) : nat_scope.
Notation "'_^_'" := (nat_op null_op bin_op) : nat_scope.
Notation "x '^' n" := (n_op null_op bin_op n x) : N_scope.
Notation "'_^_'" := (n_op null_op bin_op) : N_scope.
