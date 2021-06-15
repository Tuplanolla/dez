(* bad *)
From Maniunfold.Has Require Export
  Addition Action.
From Maniunfold.Is Require Export
  TwoSortedLeftLeftDistributive TwoSortedLeftRightDistributive.

Class IsTwoLDistr (A B : Type)
  `(HasAdd A) `(HasAdd B)
  `(HasActL A B) : Prop := {
  A_B_add_act_l_is_two_l_l_distr :> IsTwoLLDistr add act_l;
  A_B_add_act_l_is_two_l_r_distr :> IsTwoLRDistr add add act_l;
}.
