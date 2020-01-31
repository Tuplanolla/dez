From Maniunfold.Has Require Export
  EquivalenceRelation Addition Multiplication.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

Class IsLDistr {A : Type} {has_eq_rel : HasEqRel A}
  (has_add : HasAdd A) (has_mul : HasMul A) : Prop :=
  l_distr : forall x y z : A, x * (y + z) == x * y + x * z.
