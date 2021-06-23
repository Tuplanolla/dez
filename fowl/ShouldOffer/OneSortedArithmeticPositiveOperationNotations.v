From Maniunfold.Has Require Import
  Addition Multiplication.
From Maniunfold.Offers Require Import
  OneSortedPositiveOperations.
From Maniunfold.ShouldHave Require Export
  OneSortedArithmeticNotations.

Notation "'_*_'" := (positive_op add) : positive_scope.
Notation "n '*' x" := (positive_op add n x) : positive_scope.
Notation "'_^_'" := (positive_op mul) : positive_scope.
Notation "x '^' n" := (positive_op mul n x) : positive_scope.
