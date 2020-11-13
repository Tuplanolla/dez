From Maniunfold.Offers Require Export
  OneSorted.NaturalOperations.
From Maniunfold.ShouldHave Require Export
  OneSorted.AdditiveNotations.

Notation "n '*' x" := (nat_op bin_op null_op n x) : nat_scope.
Notation "n '*' x" := (n_op bin_op null_op n x) : N_scope.

Notation "'_*_'" := (nat_op bin_op null_op) (only parsing) : nat_scope.
Notation "'_*_'" := (n_op bin_op null_op) (only parsing) : N_scope.
