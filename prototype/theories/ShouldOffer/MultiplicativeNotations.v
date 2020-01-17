From Maniunfold.Offers Require Export
  PositivePowers NaturalPowers.
From Maniunfold.ShouldHave Require Export
  MultiplicativeNotations.

Notation "x '^' n" := (pop n x) : positive_scope.
Notation "x '^' n" := (nop n x) : N_scope.
