From Maniunfold.Has Require Export
  EquivalenceRelation Join Meet.
From Maniunfold.Is Require Export
  OneSorted.Semilattice OneSorted.Sorbing.
From Maniunfold.ShouldHave Require Import
  ArithmeticNotations.

(** Remember that join [\_/] is "addition" and bottom [_|_] is "zero". *)

Class IsLat {A : Type}
  (A_has_join : HasJoin A) (has_meet : HasMeet A) : Prop := {
  join_is_slat :> IsSlat join;
  meet_is_slat :> IsSlat meet;
  join_meet_is_sorb :> IsSorb join meet;
  meet_join_is_sorb :> IsSorb meet join;
}.
