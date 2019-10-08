From Maniunfold.Has Require Import EquivalenceRelation GroupOperation.
From Maniunfold.Is Require Import Setoid.

Import AdditiveNotations.

Class IsCommutative (A : Type)
  {has_eqv : HasEqv A} {has_opr : HasOpr A} : Prop := {
  eqv_is_setoid :> IsSetoid A;
  opr_commutative : forall x y : A, x + y == y + x;
}.
