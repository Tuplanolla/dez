From Maniunfold.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities.
From Maniunfold.Is Require Export
  Setoid.

Class IsLeftAbsorbing {A : Type} {has_eqv : HasEqv A}
  (has_mul : HasMul A) (has_zero : HasZero A) : Prop := {
  left_absorbing_eqv_is_setoid :> IsSetoid eqv;
  left_absorbing : forall x : A, 0 * x == 0;
}.
