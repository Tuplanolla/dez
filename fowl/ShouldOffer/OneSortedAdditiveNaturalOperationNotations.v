From DEZ.Offers Require Import
  OneSortedNaturalOperations.
From DEZ.ShouldHave Require Export
  OneSortedAdditiveNotations.

Notation "'_*_'" := (nat_op null_op bin_op) : nat_scope.
Notation "n '*' x" := (nat_op null_op bin_op n x) : nat_scope.
Notation "'_*_'" := (n_op null_op bin_op) : N_scope.
Notation "n '*' x" := (n_op null_op bin_op n x) : N_scope.
