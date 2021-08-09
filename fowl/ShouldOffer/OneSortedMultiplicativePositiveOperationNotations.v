From DEZ.Offers Require Import
  OneSortedPositiveOperations.
From DEZ.ShouldHave Require Export
  OneSortedMultiplicativeNotations.

Notation "'_^_'" := (positive_op bin_op) : positive_scope.
Notation "x '^' n" := (positive_op bin_op n x) : positive_scope.
