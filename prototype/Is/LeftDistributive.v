From Maniunfold.Has Require Export
  EquivalenceRelation FieldOperations.
From Maniunfold.Is Require Export
  Setoid.

Class IsLeftDistributive {A : Type} {has_eqv : HasEqv A}
  (has_add : HasAdd A) (has_mul : HasMul A) : Prop := {
  left_distributive_eqv_is_setoid :> IsSetoid eqv;
  left_distributive : forall x y z : A, x * (y + z) == x * y + x * z;
}.
