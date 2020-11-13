From Maniunfold.Offers Require Export
  OneSorted.IntegerOperations.
From Maniunfold.ShouldHave Require Export
  OneSorted.ArithmeticNotations.

Notation "n '*' x" := (z_op add zero neg n x) : Z_scope.
Notation "x '^' n" := (z_op mul one recip n x) : Z_scope.

Notation "'_*_'" := (z_op add zero neg) (only parsing) : Z_scope.
Notation "'_^_'" := (flip (z_op mul one recip)) (only parsing) : Z_scope.
