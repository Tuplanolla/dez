From Maniunfold.Offers Require Export
  OneSorted.PositiveOperations.
From Maniunfold.ShouldHave Require Export
  OneSorted.ArithmeticNotations.

Notation "n '*' x" := (positive_op add n x) : positive_scope.
Notation "x '^' n" := (positive_op mul n x) : positive_scope.

Notation "'_*_'" := (positive_op add) (only parsing) : positive_scope.
Notation "'_^_'" := (flip (positive_op mul)) (only parsing) : positive_scope.
