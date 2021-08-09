From DEZ.Has Require Export
  Addition Zero Negation
  Multiplication One
  Action.
From DEZ.Is Require Export
  Ring OneSortedAbelianGroup
  TwoSortedRightLeftDistributive TwoSortedRightCompatible
  TwoSortedRightUnital TwoSortedRightRightDistributive.

(** Module over a noncommutative ring; right chirality.
    See [Is.TwoSortedLeftModule]. *)

Class IsRMod (A B : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasActR A B) : Prop := {
  A_zero_neg_add_one_mul_is_ring :> IsRing zero neg add one mul;
  B_add_zero_neg_is_ab_grp :> IsAbGrp add zero neg;
  A_B_add_add_act_r_is_two_r_distr_l :> IsTwoRDistrL add add act_r;
  A_B_mul_act_r_is_r_compat :> IsRCompat mul act_r;
  A_B_zero_act_r_is_two_unl_r :> IsTwoUnlR act_r zero;
  A_B_add_act_r_is_two_r_distr_r :> IsTwoRDistrR add act_r;
}.
