From DEZ.Has Require Export
  Addition Zero Negation
  Multiplication One
  Action.
From DEZ.Is Require Export
  Ring OneSortedAbelianGroup
  TwoSortedLeftRightDistributive TwoSortedLeftCompatible
  TwoSortedLeftUnital TwoSortedLeftLeftDistributive.

(** Module over a noncommutative ring; left chirality.
    The ring is carried by [A] and the module by [B]. *)

Class IsLMod (A B : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasActL A B) : Prop := {
  A_zero_neg_add_one_mul_is_ring :> IsRing zero neg add one mul;
  B_add_zero_neg_is_ab_grp :> IsAbGrp add zero neg;
  A_B_add_add_act_l_is_two_l_distr_r :> IsTwoLDistrR add add act_l;
  A_B_mul_act_l_is_l_compat :> IsLCompat mul act_l;
  A_B_zero_act_l_is_two_unl_l :> IsTwoUnlL act_l zero;
  A_B_add_act_l_is_two_l_distr_l :> IsTwoLDistrL add act_l;
}.
