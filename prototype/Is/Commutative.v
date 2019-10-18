From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation.
From Maniunfold.Is Require Export
  Setoid.

Import AdditiveNotations.

Class IsCommutative {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) : Prop := {
  commutative_eqv_is_setoid :> IsSetoid eqv;
  commutative : forall x y : A, x + y == y + x;
}.
