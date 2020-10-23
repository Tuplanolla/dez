(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Join OneSorted.Bottom OneSorted.Meet OneSorted.Top.
From Maniunfold.Is Require Export
  OneSorted.Lattice OneSorted.Unital OneSorted.BoundedSemilattice.

Class IsBndLat (A : Type)
  `(HasJoin A) `(HasBot A)
  `(HasMeet A) `(HasTop A) : Prop := {
  A_join_meet_is_lat :> IsLat A join meet;
  A_join_bot_is_unl :> IsUnl A join bot;
  A_meet_top_is_unl :> IsUnl A meet top;
}.

Section Context.

Context {A : Type} `{IsBndLat A}.

(** TODO Not sure if this is sensible... *)

Global Instance A_join_bot_is_bnd_slat : IsBndSlat A join bot.
Proof. split; typeclasses eauto. Defined.

Global Instance A_meet_top_is_bnd_slat : IsBndSlat A meet top.
Proof. split; typeclasses eauto. Defined.

End Context.
