(* bad *)
From Maniunfold.Has Require Export
  EquivalenceRelation Join Bottom Meet Top.
From Maniunfold.Is Require Export
  OneSorted.Lattice OneSorted.Unital OneSorted.Distributive.
From Maniunfold.ShouldHave Require Import
  ArithmeticNotations.

Class IsDistrLat {A : Type}
  (A_has_join : HasJoin A) (has_bot : HasBot A)
  (A_has_meet : HasMeet A) (has_top : HasTop A) : Prop := {
  join_meet_is_lat :> IsLat join meet;
  join_meet_is_distr :> IsDistr join meet;
  meet_join_is_distr :> IsDistr meet join;
}.
