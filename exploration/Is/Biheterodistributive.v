From Maniunfold.Has Require Export
  EquivalenceRelation FieldOperations Power.
From Maniunfold.Is Require Export
  LeftHeterodistributive RightHeterodistributive.

Class IsBiheterodistributive {A : Type} {has_eqv : HasEqv A}
  (has_add : HasAdd A) (has_mul : HasMul A) (has_pow : HasPow A) : Prop := {
  add_mul_is_left_heterodistributive :> IsLeftHeterodistributive add mul pow;
  add_mul_is_right_heterodistributive :> IsRightHeterodistributive add mul pow;
}.
