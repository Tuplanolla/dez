From Maniunfold.Has Require Export
  OneSorted.Addition TwoSorted.LeftAction.
From Maniunfold.Is Require Import
  TwoSorted.LeftLeftDistributive TwoSorted.LeftRightDistributive.

Class IsTwoLDistr (A B : Type)
  (A_has_add : HasAdd A) (B_has_add : HasAdd B)
  (A_B_has_l_act : HasLAct A B) : Prop := {
  A_B_add_l_act_is_two_l_l_distr :> IsTwoLLDistr A B add l_act;
  A_B_add_l_act_is_two_l_r_distr :> IsTwoLRDistr A B add add l_act;
}.
