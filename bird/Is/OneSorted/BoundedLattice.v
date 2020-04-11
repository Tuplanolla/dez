(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Join OneSorted.Bottom OneSorted.Meet OneSorted.Top.
From Maniunfold.Is Require Export
  OneSorted.Lattice OneSorted.Unital OneSorted.BoundedSemilattice.

Class IsBndLat (A : Type)
  (A_has_join : HasJoin A) (A_has_bot : HasBot A)
  (A_has_meet : HasMeet A) (A_has_top : HasTop A) : Prop := {
  A_join_meet_is_lat :> IsLat A join meet;
  A_join_bot_is_unl :> IsUnl A join bot;
  A_meet_top_is_unl :> IsUnl A meet top;
}.

Section Context.

Context {A : Type} `{is_bnd_lat : IsBndLat A}.

(** TODO Not sure if this is sensible... *)

Global Instance A_join_bot_is_bnd_slat : IsBndSlat A join bot.
Proof. split; typeclasses eauto. Qed.

Global Instance A_meet_top_is_bnd_slat : IsBndSlat A meet top.
Proof. split; typeclasses eauto. Qed.

End Context.
