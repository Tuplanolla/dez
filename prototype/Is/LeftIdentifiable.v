From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity.
From Maniunfold.Is Require Export
  Setoid.
From Maniunfold.Supports Require Import
  AdditiveGroupNotations.

Class IsLeftIdentifiable {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) (has_idn : HasIdn A) : Prop := {
  eqv_is_setoid :> IsSetoid eqv;
  left_identifiable : forall x : A, 0 + x == x;
}.
