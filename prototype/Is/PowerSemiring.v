From Maniunfold.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities Power.
From Maniunfold.Is Require Export
  Semiring LeftHeterodistributive RightHeteroabsorbing.

Class IsPowerSemiring {A : Type} {has_eqv : HasEqv A}
  (has_add : HasAdd A) (has_zero : HasZero A)
  (has_mul : HasMul A) (has_one : HasOne A) (has_pow : HasPow A) : Prop := {
  add_zero_mul_one_is_semiring :> IsSemiring add zero mul one;
  add_mul_is_left_heterodistributive :> IsLeftHeterodistributive add mul pow;
  pow_zero_one_is_right_heteroabsorbing :> IsRightHeteroabsorbing pow zero one;
}.
