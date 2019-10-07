From Maniunfold.Has Require Import EquivalenceRelation Operation.
From Maniunfold.Is Require Import Setoid.

Import AdditiveNotations.

Class IsAssociative (A : Type)
  {has_eqv : HasEqv A} {has_opr : HasOpr A} : Prop := {
  eqv_is_setoid :> IsSetoid A;
  opr_associative : forall x y z : A, x + (y + z) == (x + y) + z;
}.
