From DEZ.Has Require Export
  EquivalenceRelation FieldOperations Power.
From DEZ.Is Require Export
  Setoid.
From DEZ.ShouldHave Require Import
  EquivalenceNotations FieldNotations PowerNotations.

Class IsLeftHeterodistributive {A : Type} {has_eqv : HasEqv A}
  (has_add : HasAdd A) (has_mul : HasMul A) (has_pow : HasPow A) : Prop := {
  eqv_is_setoid :> IsSetoid eqv;
  left_heterodistributive : forall x y z : A, x ^ (y + z) == x ^ y * x ^ z;
}.
