From DEZ.Has Require Export
  EquivalenceRelation Endomorphism.
From DEZ.Is Require Export
  Setoid.
From DEZ.ShouldHave Require Import
  EquivalenceNotations.

Class IsIdempotent {A : Type} {has_eqv : HasEqv A}
  (has_endo : HasEndo A) : Prop := {
  eqv_is_setoid :> IsSetoid eqv;
  idempotent : forall x : A, endo (endo x) == endo x;
}.
