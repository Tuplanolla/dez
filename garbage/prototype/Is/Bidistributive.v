From DEZ.Has Require Export
  EquivalenceRelation FieldOperations.
From DEZ.Is Require Export
  LeftDistributive RightDistributive.

Class IsBidistributive {A : Type} {has_eqv : HasEqv A}
  (has_add : HasAdd A) (has_mul : HasMul A) : Prop := {
  add_mul_is_left_distributive :> IsLeftDistributive add mul;
  add_mul_is_right_distributive :> IsRightDistributive add mul;
}.
