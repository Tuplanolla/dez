From Maniunfold.Has Require Import EquivalenceRelation
  GroupOperation GroupInverse.
From Maniunfold.Is Require Import Setoid.

Import AdditiveNotations.

Class IsAntidistributive (A : Type)
  {has_eqv : HasEqv A} {has_opr : HasOpr A} {has_inv : HasInv A} : Prop := {
  eqv_is_setoid :> IsSetoid A;
  inv_antidistributive : forall x y : A, - (x + y) == (- y) + (- x);
}.
