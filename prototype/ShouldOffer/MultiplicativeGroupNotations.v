From Maniunfold.Offers Require Export
  PositivePowers NaturalPowers IntegerPowers.
From Maniunfold.ShouldHave Require Export
  MultiplicativeGroupNotations.

Notation "x '^' n" := (popr n x) : positive_scope.
Notation "x '^' n" := (nopr n x) : N_scope.
Notation "x '^' n" := (zopr n x) : Z_scope.
