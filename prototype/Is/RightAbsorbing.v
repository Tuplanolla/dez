From Maniunfold.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities.
From Maniunfold.Is Require Export
  Setoid.
From Maniunfold.Supports Require Import
  FieldNotations.

Class IsRightAbsorbing {A : Type} {has_eqv : HasEqv A}
  (has_mul : HasMul A) (has_zero : HasZero A) : Prop := {
  eqv_is_setoid :> IsSetoid eqv;
  right_absorbing : forall x : A, x * 0 == 0;
}.
