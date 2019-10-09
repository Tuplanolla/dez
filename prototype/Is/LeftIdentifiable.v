From Maniunfold.Has Require Import EquivalenceRelation
  GroupOperation GroupIdentity.
From Maniunfold.Is Require Import Setoid.

Import AdditiveNotations.

Class IsLeftIdentifiable (A : Type)
  {has_eqv : HasEqv A} {has_opr : HasOpr A} {has_idn : HasIdn A} : Prop := {
  eqv_is_setoid :> IsSetoid A;
  opr_left_identifiable : forall x : A, 0 + x == x;
}.
