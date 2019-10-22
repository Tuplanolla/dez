From Maniunfold.Has Require Export
  EquivalenceRelation FieldOperations.
From Maniunfold.Is Require Export
  Setoid.
From Maniunfold.Supports Require Import
  FieldNotations.

Class IsRightDistributive {A : Type} {has_eqv : HasEqv A}
  (has_add : HasAdd A) (has_mul : HasMul A) : Prop := {
  eqv_is_setoid :> IsSetoid eqv;
  right_distributive : forall x y z : A, (x + y) * z == x * z + y * z;
}.
