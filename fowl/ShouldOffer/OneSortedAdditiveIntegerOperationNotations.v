From Maniunfold.Offers Require Export
  OneSortedIntegerOperations.
From Maniunfold.ShouldHave Require Export
  OneSortedAdditiveNotations.

Notation "n '*' x" := (z_op bin_op null_op un_op n x) : Z_scope.

Notation "'_*_'" := (z_op bin_op null_op un_op) (only parsing) : Z_scope.
