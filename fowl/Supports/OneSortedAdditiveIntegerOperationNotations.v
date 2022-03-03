From DEZ.Justifies Require Import
  OneSortedIntegerOperations.
From DEZ.Supports Require Export
  OneSortedAdditiveNotations.

Notation "'_*_'" := (z_op null_op un_op bin_op) : Z_scope.
Notation "n '*' x" := (z_op null_op un_op bin_op n x) : Z_scope.
