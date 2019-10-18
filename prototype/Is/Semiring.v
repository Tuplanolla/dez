From Maniunfold.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities.
From Maniunfold.Is Require Export
  CommutativeMonoid Monoid Distributive.

Class IsSemiring {A : Type} {has_eqv : HasEqv A}
  (has_add : HasAdd A) (has_zero : HasZero A)
  (has_mul : HasMul A) (has_one : HasOne A) : Prop := {
  semiring_add_zero_is_commutative_monoid :> IsCommutativeMonoid add zero;
  semiring_mul_one_is_monoid :> IsMonoid mul one;
  semiring_add_mul_is_distributive :> IsDistributive add mul;
}.
