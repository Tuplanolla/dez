From DEZ.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity.
From DEZ.Is Require Export
  Setoid.
From DEZ.ShouldHave Require Import
  AdditiveGroupNotations.

Class IsLeftIdentifiable {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) (has_idn : HasIdn A) : Prop := {
  eqv_is_setoid :> IsSetoid eqv;
  left_identifiable : forall x : A, 0 + x == x;
}.
