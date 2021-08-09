From DEZ.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities.
From DEZ.Is Require Export
  LeftAbsorbing RightAbsorbing.

Class IsBiabsorbing {A : Type} {has_eqv : HasEqv A}
  (has_mul : HasMul A) (has_zero : HasZero A) : Prop := {
  mul_zero_is_left_absorbing :> IsLeftAbsorbing mul zero;
  mul_zero_is_right_absorbing :> IsRightAbsorbing mul zero;
}.
