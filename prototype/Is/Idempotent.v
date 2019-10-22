From Maniunfold.Has Require Export
  EquivalenceRelation Endomorphism.
From Maniunfold.Is Require Export
  Setoid.
From Maniunfold.Supports Require Import
  EquivalenceNotations.

Class IsIdempotent {A : Type} {has_eqv : HasEqv A}
  (has_endo : HasEndo A) : Prop := {
  eqv_is_setoid :> IsSetoid eqv;
  idempotent : forall x : A, endo (endo x) == endo x;
}.
