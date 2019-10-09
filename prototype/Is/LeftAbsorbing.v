From Maniunfold.Has Require Import EquivalenceRelation
  FieldOperations FieldIdentities.
From Maniunfold.Is Require Import Setoid.

Class IsLeftAbsorbing (A : Type)
  {has_eqv : HasEqv A} {has_mul : HasMul A} {has_zero : HasZero A} : Prop := {
  eqv_is_setoid :> IsSetoid A;
  opr_left_absorbing : forall x : A, 0 * x == 0;
}.
