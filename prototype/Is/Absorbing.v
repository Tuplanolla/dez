From Maniunfold.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities.
From Maniunfold.Is Require Export
  LeftAbsorbing RightAbsorbing.

Class IsAbsorbing (A : Type)
  {has_eqv : HasEqv A} {has_mul : HasMul A} {has_zero : HasZero A} : Prop := {
  opr_is_left_absorbing :> IsLeftAbsorbing A;
  opr_is_right_absorbing :> IsRightAbsorbing A;
}.
