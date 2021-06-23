From Maniunfold.Has Require Import
  Addition Zero Negation Multiplication One Reciprocation.
From Maniunfold.Offers Require Import
  OneSortedIntegerOperations.
From Maniunfold.ShouldHave Require Export
  OneSortedArithmeticNotations.

Notation "'_*_'" := (z_op add zero neg) : Z_scope.
Notation "n '*' x" := (z_op add zero neg n x) : Z_scope.
Notation "'_^_'" := (z_op mul one recip) : Z_scope.
Notation "x '^' n" := (z_op mul one recip n x) : Z_scope.
