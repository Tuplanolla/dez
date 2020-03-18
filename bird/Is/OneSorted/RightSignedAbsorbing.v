From Maniunfold.Has Require Export
  EquivalenceRelation Negation Multiplication One.
From Maniunfold.ShouldHave Require Import
  ArithmeticNotations.

Class IsRSgnAbsorb {A : Type}
  (A_has_neg : HasNeg A) (has_mul : HasMul A) (has_one : HasOne A) : Prop :=
  r_sgn_absorb : forall x : A, x * (- (1)) = - x.
