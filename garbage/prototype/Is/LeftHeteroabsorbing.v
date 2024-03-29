From DEZ.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities Power.
From DEZ.Is Require Export
  Setoid.
From DEZ.ShouldHave Require Import
  FieldNotations PowerNotations.

Class IsLeftHeteroabsorbing {A : Type} {has_eqv : HasEqv A}
  (has_pow : HasPow A) (has_zero : HasZero A) (has_one : HasOne A) : Prop := {
  eqv_is_setoid :> IsSetoid eqv;
  left_heteroabsorbing : forall x : A, 0 ^ x == 1;
}.
