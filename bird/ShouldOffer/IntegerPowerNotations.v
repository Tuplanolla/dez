From Maniunfold.Offers Require Export
  PositivePowers NaturalPowers IntegerPowers.
From Maniunfold.ShouldHave Require Export
  AdditiveNotations.

Reserved Notation "n '*' x" (at level 40, left associativity).
Reserved Notation "x '^' n" (at level 30, right associativity).

Notation "n '*' x" := (positive_op n x) : positive_scope.
Notation "n '*' x" := (nat_op n x) : nat_scope.
Notation "n '*' x" := (n_op n x) : N_scope.
Notation "n '*' x" := (z_op n x) : Z_scope.

Notation "x '^' n" := (positive_op n x) : positive_scope.
Notation "x '^' n" := (nat_op n x) : nat_scope.
Notation "x '^' n" := (n_op n x) : N_scope.
Notation "x '^' n" := (z_op n x) : Z_scope.
