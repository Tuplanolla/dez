From Maniunfold.Offers Require Export
  OneSorted.PositiveOperations OneSorted.NaturalOperations
  OneSorted.IntegerOperations.
From Maniunfold.ShouldHave Require Export
  OneSorted.ArithmeticNotations.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "n '*' x" (at level 40, left associativity).
Reserved Notation "x '^' n" (at level 30, right associativity).

Reserved Notation "'_*_'" (at level 0, no associativity).
Reserved Notation "'_^_'" (at level 0, no associativity).

Notation "n '*' x" := (positive_op add n x) : positive_scope.
Notation "'_*_'" := (positive_op add) (only parsing) : positive_scope.
Notation "n '*' x" := (nat_op add zero n x) : nat_scope.
Notation "'_*_'" := (nat_op add zero) (only parsing) : nat_scope.
Notation "n '*' x" := (n_op add zero n x) : N_scope.
Notation "'_*_'" := (n_op add zero) (only parsing) : N_scope.
Notation "n '*' x" := (z_op add zero neg n x) : Z_scope.
Notation "'_*_'" := (z_op add zero neg) (only parsing) : Z_scope.
Notation "x '^' n" := (positive_op mul n x) : positive_scope.
Notation "'_^_'" := (flip (positive_op mul)) (only parsing) : positive_scope.
Notation "x '^' n" := (nat_op mul one n x) : nat_scope.
Notation "'_^_'" := (flip (nat_op mul one)) (only parsing) : nat_scope.
Notation "x '^' n" := (n_op mul one n x) : N_scope.
Notation "'_^_'" := (flip (n_op mul one)) (only parsing) : N_scope.
Notation "x '^' n" := (z_op mul one recip n x) : Z_scope.
Notation "'_^_'" := (flip (z_op mul one recip)) (only parsing) : Z_scope.
