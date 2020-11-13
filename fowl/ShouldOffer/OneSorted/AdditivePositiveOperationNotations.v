From Maniunfold.Offers Require Export
  OneSorted.PositiveOperations.
From Maniunfold.ShouldHave Require Export
  OneSorted.AdditiveNotations.

Notation "n '*' x" := (positive_op bin_op n x) : positive_scope.

Notation "'_*_'" := (positive_op bin_op) (only parsing) : positive_scope.
