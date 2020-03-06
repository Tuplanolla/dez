From Maniunfold.Has Require Export
  EquivalenceRelation Join Bottom Meet Top.
From Maniunfold.Is Require Export
  OneSortedly.Lattice OneSortedly.Unital.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

Class IsBndLat {A : Type} {has_eq_rel : HasEqRel A}
  (has_join : HasJoin A) (has_bot : HasBot A)
  (has_meet : HasMeet A) (has_top : HasTop A) : Prop := {
  join_meet_is_lat :> IsLat join meet;
  join_bot_is_unl :> IsUnl join bot;
  meet_top_is_unl :> IsUnl meet top;
}.
