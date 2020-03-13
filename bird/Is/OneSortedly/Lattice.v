From Maniunfold.Has Require Export
  EquivalenceRelation Join Meet.
From Maniunfold.Is Require Export
  OneSortedly.Semilattice OneSortedly.Sorbing.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

(** Remember that join [\_/] is "addition" and bottom [_|_] is "zero". *)

Class IsLat {A : Type}
  (has_join : HasJoin A) (has_meet : HasMeet A) : Prop := {
  join_is_slat :> IsSlat join;
  meet_is_slat :> IsSlat meet;
  join_meet_is_sorb :> IsSorb join meet;
  meet_join_is_sorb :> IsSorb meet join;
}.
