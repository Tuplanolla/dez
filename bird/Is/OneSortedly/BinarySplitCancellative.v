From Maniunfold.Has Require Export
  EquivalenceRelation Negation Multiplication.
From Maniunfold.ShouldHave Require Import
  ArithmeticNotations.

Class IsBinSptCancel {A : Type}
  (has_neg : HasNeg A) (has_mul : HasMul A) : Prop :=
  bin_spt_cancel : forall x y : A, (- x) * (- y) = x * y.
