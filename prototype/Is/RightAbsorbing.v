From Maniunfold.Has Require Import EquivalenceRelation
  FieldOperations FieldIdentities.
From Maniunfold.Is Require Import Setoid.

Class IsRightAbsorbing (A : Type)
  {has_eqv : HasEqv A} {has_mul : HasMul A} {has_zero : HasZero A} : Prop := {
  eqv_is_setoid :> IsSetoid A;
  opr_right_absorbing : forall x : A, x * 0 == 0;
}.
