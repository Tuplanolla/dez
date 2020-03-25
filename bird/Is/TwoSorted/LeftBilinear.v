From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.Addition TwoSorted.LeftAction.
From Maniunfold.Is Require Import
  TwoSorted.LeftDistributive ThreeSorted.Bicompatible TwoSorted.LeftLinear.

(** TODO Check this and find a justification for the higher-sortedness. *)

Class IsLBilin {A B : Type}
  (A_has_add : HasAdd A) (B_has_add : HasAdd B)
  (A_B_has_l_act : HasLAct A B) : Prop := {
  add_add_l_act_is_two_l_distr :> IsTwoLDistr add add l_act;
  add_l_act_is_bicompat :> IsBicompat add l_act;
  l_act_add_is_bicompat :> IsBicompat l_act add;
}.

(** TODO Bilinear forms are symmetric bilinear maps, so why not say so. *)

(*
Class IsLBilin' {A B : Type}
  (A_has_add : HasAdd A) (B_has_add : HasAdd B)
  (A_B_has_l_act : HasLAct A B) : Prop := {
  add_is_l_lin :> forall y : _, IsLLin add (fun x => x + y) l_act;
  flip_add_is_l_lin :> forall x : _, IsLLin add (fun y => x + y) l_act;
}.
*)
