From Maniunfold.Has Require Import EquivalenceRelation Operation Identity.
From Maniunfold.Is Require Import Setoid.

Import AdditiveNotations.

Class IsRightIdentity (A : Type)
  {has_eqv : HasEqv A} {has_opr : HasOpr A} {has_idn : HasIdn A} : Prop := {
  eqv_is_setoid :> IsSetoid A;
  opr_right_identity : forall x : A, x + 0 == x;
}.
