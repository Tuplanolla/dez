From Maniunfold.Offers Require Export
  OneSortedPositiveOperations.
From Maniunfold.ShouldHave Require Export
  OneSortedAdditiveNotations.

Notation "n '*' x" := (positive_op bin_op n x) : positive_scope.

Notation "'_*_'" := (positive_op bin_op) (only parsing) : positive_scope.
