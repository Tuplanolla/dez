From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.Addition TwoSorted.LeftAction.
From Maniunfold.Is Require Import
  TwoSorted.LeftDistributive ThreeSorted.Bicompatible.

(** TODO Check this and find a justification for the higher-sortedness. *)

Class IsLBilin {A B : Type}
  (A_has_add : HasAdd A) (B_has_add : HasAdd B)
  (A_B_has_l_act : HasLAct A B) : Prop := {
  a :> IsTwoLDistr add add l_act;
  b :> IsBicompat add l_act;
  c :> IsBicompat l_act add;
}.
