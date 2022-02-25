From DEZ.Provides Require Import
  OneSortedPositiveOperations.
From DEZ.Supports Require Export
  OneSortedAdditiveNotations.

Notation "'_*_'" := (positive_op bin_op) : positive_scope.
Notation "n '*' x" := (positive_op bin_op n x) : positive_scope.
