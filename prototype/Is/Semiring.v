From Maniunfold.Has Require Import EquivalenceRelation
  FieldOperations FieldIdentities.
From Maniunfold.Is Require Import Setoid Monoid CommutativeMonoid
  LeftDistributive RightDistributive.

Class IsSemiring (A : Type) {has_eqv : HasEqv A}
  {has_add : HasAdd A} {has_zero : HasZero A}
  {has_mul : HasMul A} {has_one : HasOne A} : Prop := {
  add_is_commutative_monoid :> IsCommutativeMonoid A
    (has_opr := has_add) (has_idn := has_zero);
  mul_is_monoid :> IsMonoid A
    (has_opr := has_mul) (has_idn := has_one);
  mul_add_is_left_distributive :> IsLeftDistributive A;
  mul_add_is_right_distributive :> IsRightDistributive A;
}.
