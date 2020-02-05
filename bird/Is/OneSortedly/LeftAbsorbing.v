From Maniunfold.Has Require Export
  EquivalenceRelation Zero Multiplication.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

Class IsLAbsorb {A : Type} {has_eq_rel : HasEqRel A}
  (has_zero : HasZero A) (has_mul : HasMul A) : Prop :=
  l_absorb : forall x : A, 0 * x == 0.
