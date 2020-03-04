From Maniunfold.Has Require Export
  EquivalenceRelation Negation Multiplication.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

Class IsBinCrs {A : Type} {has_eq_rel : HasEqRel A}
  (has_neg : HasNeg A) (has_mul : HasMul A) : Prop :=
  bin_crs : forall x y : A, (- x) * y == x * (- y).
