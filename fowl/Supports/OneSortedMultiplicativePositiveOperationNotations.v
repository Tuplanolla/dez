From DEZ.Justifies Require Import
  OneSortedPositiveOperations.
From DEZ.Supports Require Export
  OneSortedMultiplicativeNotations.

Notation "'_^_'" := (positive_op bin_op) : positive_scope.
Notation "x '^' n" := (positive_op bin_op n x) : positive_scope.
