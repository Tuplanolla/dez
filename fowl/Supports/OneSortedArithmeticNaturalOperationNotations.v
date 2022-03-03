From DEZ.Has Require Import
  Addition Zero Multiplication One.
From DEZ.Justifies Require Import
  OneSortedNaturalOperations.
From DEZ.Supports Require Export
  OneSortedArithmeticNotations.

Notation "'_*_'" := (nat_op zero add) : nat_scope.
Notation "n '*' x" := (nat_op zero add n x) : nat_scope.
Notation "'_*_'" := (n_op zero add) : N_scope.
Notation "n '*' x" := (n_op zero add n x) : N_scope.
Notation "'_^_'" := (nat_op one mul) : nat_scope.
Notation "x '^' n" := (nat_op one mul n x) : nat_scope.
Notation "'_^_'" := (n_op one mul) : N_scope.
Notation "x '^' n" := (n_op one mul n x) : N_scope.
