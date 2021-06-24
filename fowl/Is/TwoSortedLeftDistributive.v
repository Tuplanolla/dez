(* bad *)
From Maniunfold.Has Require Export
  Addition Action.
From Maniunfold.Is Require Export
  TwoSortedLeftLeftDistributive TwoSortedLeftRightDistributive.

Class IsTwoDistrL (A B : Type)
  `(HasAdd A) `(HasAdd B)
  `(HasActL A B) : Prop := {
  A_B_add_act_l_is_two_l_distr_l :> IsTwoLDistrL add act_l;
  A_B_add_act_l_is_two_l_distr_r :> IsTwoLDistrR add add act_l;
}.
