From Maniunfold.Has Require Import EquivalenceRelation FieldOperations.
From Maniunfold.Is Require Import Setoid.

(** TODO Merge modules for left and right chiralities. *)

Class IsLeftDistributive (A : Type) {has_eqv : HasEqv A}
  {has_add : HasAdd A} {has_mul : HasMul A} : Prop := {
  eqv_is_setoid :> IsSetoid A;
  mul_add_left_distributive : forall x y z : A, x * (y + z) == x * y + x * z;
}.
