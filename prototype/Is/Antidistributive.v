From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation GroupInverse.
From Maniunfold.Is Require Export
  Setoid.

Import AdditiveNotations.

Class IsAntidistributive {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) (has_inv : HasInv A) : Prop := {
  antidistributive_eqv_is_setoid :> IsSetoid eqv;
  antidistributive : forall x y : A, - (x + y) == (- y) + (- x);
}.
