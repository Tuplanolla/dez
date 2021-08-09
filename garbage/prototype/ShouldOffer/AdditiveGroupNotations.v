From DEZ.Offers Require Export
  PositivePowers NaturalPowers IntegerPowers.
From DEZ.ShouldHave Require Export
  AdditiveGroupNotations.

Notation "n '*' x" := (popr n x) : positive_scope.
Notation "n '*' x" := (nopr n x) : N_scope.
Notation "n '*' x" := (zopr n x) : Z_scope.
