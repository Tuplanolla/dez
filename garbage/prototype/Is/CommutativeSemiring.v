From Maniunfold.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities.
From Maniunfold.Is Require Export
  Setoid Semiring Commutative.

Class IsCommutativeSemiring {A : Type} {has_eqv : HasEqv A}
  (has_add : HasAdd A) (has_zero : HasZero A)
  (has_mul : HasMul A) (has_one : HasOne A) : Prop := {
  add_zero_mul_one_is_semiring :> IsSemiring add zero mul one;
  mul_is_commutative :> IsCommutative mul;
}.
