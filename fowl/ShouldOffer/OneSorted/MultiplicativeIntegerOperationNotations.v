From Maniunfold.Offers Require Export
  OneSorted.IntegerOperations.
From Maniunfold.ShouldHave Require Export
  OneSorted.MultiplicativeNotations.

Notation "x '^' n" := (z_op bin_op null_op un_op n x) : Z_scope.

Notation "'_^_'" := (flip (z_op bin_op null_op un_op))
  (only parsing) : Z_scope.
