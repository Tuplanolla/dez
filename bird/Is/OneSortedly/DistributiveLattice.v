From Maniunfold.Has Require Export
  EquivalenceRelation Join Bottom Meet Top.
From Maniunfold.Is Require Export
  OneSortedly.Lattice OneSortedly.Unital OneSortedly.Distributive.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

Class IsDistrLat {A : Type}
  (has_join : HasJoin A) (has_bot : HasBot A)
  (has_meet : HasMeet A) (has_top : HasTop A) : Prop := {
  join_meet_is_lat :> IsLat join meet;
  join_meet_is_distr :> IsDistr join meet;
  meet_join_is_distr :> IsDistr meet join;
}.
