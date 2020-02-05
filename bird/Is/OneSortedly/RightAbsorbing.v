From Maniunfold.Has Require Export
  EquivalenceRelation Zero Multiplication.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

Class IsRAbsorb {A : Type} {has_eq_rel : HasEqRel A}
  (has_zero : HasZero A) (has_mul : HasMul A) : Prop :=
  r_absorb : forall x : A, x * 0 == 0.
