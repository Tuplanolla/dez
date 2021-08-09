From DEZ.Offers Require Export
  PositivePowers NaturalPowers IntegerPowers.
From DEZ.ShouldHave Require Export
  MultiplicativeGroupNotations.

Notation "x '^' n" := (popr n x) : positive_scope.
Notation "x '^' n" := (nopr n x) : N_scope.
Notation "x '^' n" := (zopr n x) : Z_scope.
