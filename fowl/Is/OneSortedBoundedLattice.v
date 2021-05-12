(* bad *)
From Maniunfold.Has Require Export
  OneSortedJoin OneSortedBottom OneSortedMeet OneSortedTop.
From Maniunfold.Is Require Export
  OneSortedLattice OneSortedUnital OneSortedBoundedSemilattice.

Class IsBndLat (A : Type)
  `(HasJoin A) `(HasBot A)
  `(HasMeet A) `(HasTop A) : Prop := {
  A_join_meet_is_lat :> IsLat join meet;
  A_join_bot_is_unl :> IsUnl join bot;
  A_meet_top_is_unl :> IsUnl meet top;
}.

Section Context.

Context (A : Type) `{IsBndLat A}.

(** TODO Not sure if this is sensible... *)

Global Instance A_join_bot_is_bnd_slat : IsBndSlat join bot.
Proof. split; typeclasses eauto. Defined.

Global Instance A_meet_top_is_bnd_slat : IsBndSlat meet top.
Proof. split; typeclasses eauto. Defined.

End Context.
