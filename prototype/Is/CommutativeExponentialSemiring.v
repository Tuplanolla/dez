From Maniunfold.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities Power.
From Maniunfold.Is Require Export
  ExponentialSemiring Commutative.

Class IsCommutativeExponentialSemiring {A : Type} {has_eqv : HasEqv A}
  (has_add : HasAdd A) (has_zero : HasZero A)
  (has_mul : HasMul A) (has_one : HasOne A) (has_pow : HasPow A) : Prop := {
  add_zero_mul_one_is_exponential_semiring :>
    IsExponentialSemiring add zero mul one pow;
  mul_is_commutative :> IsCommutative mul;
}.
