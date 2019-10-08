From Maniunfold.Has Require Import EquivalenceRelation FieldOperations.
From Maniunfold.Is Require Export LeftDistributive RightDistributive.

Class IsDistributive (A : Type) {has_eqv : HasEqv A}
  {has_add : HasAdd A} {has_mul : HasMul A} : Prop := {
  mul_add_is_left_distributive :> IsLeftDistributive A;
  mul_add_is_right_distributive :> IsRightDistributive A;
}.
