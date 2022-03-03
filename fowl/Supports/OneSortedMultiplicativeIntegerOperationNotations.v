From DEZ.Justifies Require Import
  OneSortedIntegerOperations.
From DEZ.Supports Require Export
  OneSortedMultiplicativeNotations.

Notation "'_^_'" := (z_op null_op un_op bin_op) : Z_scope.
Notation "x '^' n" := (z_op null_op un_op bin_op n x) : Z_scope.
