From Maniunfold.Has Require Export
  EquivalenceRelation Addition Multiplication.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

Class IsRDistr {A : Type}
  (has_add : HasAdd A) (has_mul : HasMul A) : Prop :=
  r_distr : forall x y z : A, (x + y) * z = x * z + y * z.
