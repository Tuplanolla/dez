From Maniunfold.Offers Require Export
  PositivePowers NaturalPowers.
From Maniunfold.ShouldHave Require Export
  AdditiveNotations.

Notation "n '*' x" := (pop n x) : positive_scope.
Notation "n '*' x" := (nop n x) : N_scope.
