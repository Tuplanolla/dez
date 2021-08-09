From DEZ.Has Require Export
  EquivalenceRelation Distance.
From DEZ.Is Require Export
  Setoid.
From DEZ.ShouldHave Require Import
  EquivalenceNotations.

Class IsHeterocommutative {A B : Type} {has_eqv : HasEqv B}
  (has_dist : HasDist A B) : Prop := {
  eqv_is_setoid :> IsSetoid eqv;
  heterocommutative : forall x y : A, dist x y == dist y x;
}.
