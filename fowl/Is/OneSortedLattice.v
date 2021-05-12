(* bad *)
From Maniunfold.Has Require Export
  OneSortedJoin OneSortedMeet.
From Maniunfold.Is Require Export
  OneSortedSemilattice OneSortedSorbing.

Class IsLat (A : Type)
  `(HasJoin A) `(HasMeet A) : Prop := {
  A_join_is_slat :> IsSlat join;
  A_meet_is_slat :> IsSlat meet;
  A_join_meet_is_sorb :> IsSorb join meet;
  A_meet_join_is_sorb :> IsSorb meet join;
}.
