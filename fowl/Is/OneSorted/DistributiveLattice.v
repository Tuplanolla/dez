(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Join OneSorted.Bottom OneSorted.Meet OneSorted.Top.
From Maniunfold.Is Require Export
  OneSorted.Lattice OneSorted.Unital OneSorted.Distributive.

Class IsDistrLat (A : Type)
  `(HasJoin A) `(HasBot A)
  `(HasMeet A) `(HasTop A) : Prop := {
  A_join_meet_is_lat :> IsLat A join meet;
  A_join_meet_is_distr :> IsDistr A join meet;
  A_meet_join_is_distr :> IsDistr A meet join;
}.
