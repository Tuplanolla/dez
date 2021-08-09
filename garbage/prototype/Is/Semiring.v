From DEZ.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities.
From DEZ.Is Require Export
  CommutativeMonoid Monoid Bidistributive.

Class IsSemiring {A : Type} {has_eqv : HasEqv A}
  (has_add : HasAdd A) (has_zero : HasZero A)
  (has_mul : HasMul A) (has_one : HasOne A) : Prop := {
  add_zero_is_commutative_monoid :> IsCommutativeMonoid add zero;
  mul_one_is_monoid :> IsMonoid mul one;
  add_mul_is_distributive :> IsBidistributive add mul;
}.
