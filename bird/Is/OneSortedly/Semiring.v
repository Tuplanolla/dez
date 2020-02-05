From Maniunfold.Has Require Export
  EquivalenceRelation Addition Multiplication.
From Maniunfold.Is Require Export
  Commutative Monoid Distributive Absorbing.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

Class IsSring {A : Type} {has_eq_rel : HasEqRel A}
  (has_add : HasAdd A) (has_zero : HasZero A)
  (has_mul : HasMul A) (has_one : HasOne A) : Prop := {
  add_is_comm :> IsComm add;
  add_zero_is_mon :> IsMon add zero;
  add_mul_is_distr :> IsDistr add mul;
  zero_mul_is_absorb :> IsAbsorb zero mul;
  mul_one_is_mon :> IsMon mul one;
}.
