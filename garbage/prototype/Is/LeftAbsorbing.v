From DEZ.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities.
From DEZ.Is Require Export
  Setoid.
From DEZ.ShouldHave Require Import
  FieldNotations.

Class IsLeftAbsorbing {A : Type} {has_eqv : HasEqv A}
  (has_mul : HasMul A) (has_zero : HasZero A) : Prop := {
  eqv_is_setoid :> IsSetoid eqv;
  left_absorbing : forall x : A, 0 * x == 0;
}.
