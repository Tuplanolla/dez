From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity GroupInverse.
From Maniunfold.Is Require Export
  Setoid.

Import AdditiveNotations.

Class IsLeftInvertible (A : Type) {has_eqv : HasEqv A}
  {has_opr : HasOpr A} {has_idn : HasIdn A} {has_inv : HasInv A} : Prop := {
  left_invertible_is_setoid :> IsSetoid A;
  left_invertible : forall x : A, (- x) + x == 0;
}.
