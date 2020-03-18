From Maniunfold.Has Require Export
  EquivalenceRelation Negation Multiplication One.
From Maniunfold.ShouldHave Require Import
  ArithmeticNotations.

Class IsLSgnAbsorb {A : Type}
  (A_has_neg : HasNeg A) (has_mul : HasMul A) (has_one : HasOne A) : Prop :=
  l_sgn_absorb : forall x : A, (- (1)) * x = - x.
