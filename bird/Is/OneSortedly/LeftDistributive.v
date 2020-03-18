From Maniunfold.Has Require Export
  EquivalenceRelation Addition Multiplication.
From Maniunfold.ShouldHave Require Import
  ArithmeticNotations.

Class IsLDistr {A : Type}
  (has_add : HasAdd A) (has_mul : HasMul A) : Prop :=
  l_distr : forall x y z : A, x * (y + z) = x * y + x * z.
