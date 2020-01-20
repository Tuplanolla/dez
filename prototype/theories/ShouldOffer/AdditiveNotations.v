From Maniunfold.Offers Require Export
  PositivePowers NaturalPowers IntegerPowers.
From Maniunfold.ShouldHave Require Export
  AdditiveNotations.

Notation "n '*' x" := (p_op n x) : positive_scope.
Notation "n '*' x" := (n_op n x) : N_scope.
Notation "n '*' x" := (z_op n x) : Z_scope.
