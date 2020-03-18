From Maniunfold.Has Require Export
  EquivalenceRelation Zero Multiplication.
From Maniunfold.ShouldHave Require Import
  ArithmeticNotations.

Class IsRAbsorb {A : Type}
  (A_has_zero : HasZero A) (has_mul : HasMul A) : Prop :=
  r_absorb : forall x : A, x * 0 = 0.
