From Maniunfold.Offers Require Export
  OneSorted.PositiveOperations.
From Maniunfold.ShouldHave Require Export
  OneSorted.MultiplicativeNotations.

Notation "x '^' n" := (positive_op bin_op n x) : positive_scope.

Notation "'_^_'" := (flip (positive_op bin_op))
  (only parsing) : positive_scope.
