(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition TwoSorted.LeftAction.
From Maniunfold.Is Require Export
  TwoSorted.LeftLeftDistributive TwoSorted.LeftRightDistributive.

Class IsTwoLDistr (A B : Type)
  `(HasAdd A) `(HasAdd B)
  `(HasLAct A B) : Prop := {
  A_B_add_l_act_is_two_l_l_distr :> IsTwoLLDistr add l_act;
  A_B_add_l_act_is_two_l_r_distr :> IsTwoLRDistr add add l_act;
}.
