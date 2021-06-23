From Maniunfold.Offers Require Import
  OneSortedIntegerOperations.
From Maniunfold.ShouldHave Require Export
  OneSortedAdditiveNotations.

Notation "'_*_'" := (z_op bin_op null_op un_op) : Z_scope.
Notation "n '*' x" := (z_op bin_op null_op un_op n x) : Z_scope.
