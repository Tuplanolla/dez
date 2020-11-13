From Maniunfold.Offers Require Export
  OneSorted.NaturalOperations.
From Maniunfold.ShouldHave Require Export
  OneSorted.ArithmeticNotations.

Notation "n '*' x" := (nat_op add zero n x) : nat_scope.
Notation "n '*' x" := (n_op add zero n x) : N_scope.
Notation "x '^' n" := (nat_op mul one n x) : nat_scope.
Notation "x '^' n" := (n_op mul one n x) : N_scope.

Notation "'_*_'" := (nat_op add zero) (only parsing) : nat_scope.
Notation "'_*_'" := (n_op add zero) (only parsing) : N_scope.
Notation "'_^_'" := (flip (nat_op mul one)) (only parsing) : nat_scope.
Notation "'_^_'" := (flip (n_op mul one)) (only parsing) : N_scope.
