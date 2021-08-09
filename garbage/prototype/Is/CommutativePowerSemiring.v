From DEZ.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities Power.
From DEZ.Is Require Export
  PowerSemiring Commutative.

Class IsCommutativePowerSemiring {A : Type} {has_eqv : HasEqv A}
  (has_add : HasAdd A) (has_zero : HasZero A)
  (has_mul : HasMul A) (has_one : HasOne A) (has_pow : HasPow A) : Prop := {
  add_zero_mul_one_is_power_semiring :> IsPowerSemiring add zero mul one pow;
  mul_is_commutative :> IsCommutative mul;
}.
