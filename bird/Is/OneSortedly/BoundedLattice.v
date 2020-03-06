From Maniunfold.Has Require Export
  EquivalenceRelation Join Bottom Meet Top.
From Maniunfold.Is Require Export
  OneSortedly.Lattice OneSortedly.Unital OneSortedly.BoundedSemilattice.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

Class IsBndLat {A : Type} {has_eq_rel : HasEqRel A}
  (has_join : HasJoin A) (has_bot : HasBot A)
  (has_meet : HasMeet A) (has_top : HasTop A) : Prop := {
  join_meet_is_lat :> IsLat join meet;
  join_bot_is_unl :> IsUnl join bot;
  meet_top_is_unl :> IsUnl meet top;
}.

Section Context.

Context {A : Type} `{is_bnd_lat : IsBndLat A}.

(** TODO Not sure if this is sensible... *)

Global Instance join_bot_is_bnd_slat : IsBndSlat join bot.
Proof. constructor; typeclasses eauto. Qed.

Global Instance meet_top_is_bnd_slat : IsBndSlat meet top.
Proof. constructor; typeclasses eauto. Qed.

End Context.
