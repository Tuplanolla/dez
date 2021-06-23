From Maniunfold.Offers Require Import
  OneSortedPositiveOperations.
From Maniunfold.ShouldHave Require Export
  OneSortedMultiplicativeNotations.

Notation "'_^_'" := (positive_op bin_op) : positive_scope.
Notation "x '^' n" := (positive_op bin_op n x) : positive_scope.
