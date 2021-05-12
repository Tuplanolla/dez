(* bad *)
From Maniunfold.Has Require Export
  OneSortedJoin OneSortedBottom OneSortedMeet OneSortedTop.
From Maniunfold.Is Require Export
  OneSortedLattice OneSortedUnital OneSortedDistributive.

Class IsDistrLat (A : Type)
  `(HasJoin A) `(HasBot A)
  `(HasMeet A) `(HasTop A) : Prop := {
  A_join_meet_is_lat :> IsLat join meet;
  A_join_meet_is_distr :> IsDistr join meet;
  A_meet_join_is_distr :> IsDistr meet join;
}.
