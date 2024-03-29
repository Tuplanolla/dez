From DEZ.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities FieldInverses.
From DEZ.Is Require Export
  Ring.
From DEZ.ShouldHave Require Import
  FieldNotations.

Class IsNontrivialRing {A : Type} {has_eqv : HasEqv A}
  (has_add : HasAdd A) (has_zero : HasZero A) (has_neg : HasNeg A)
  (has_mul : HasMul A) (has_one : HasOne A) : Prop := {
  add_zero_neg_mul_one_is_ring :> IsRing add zero neg mul one;
  nontrivial : 1 =/= 0;
}.
