From Maniunfold.Has Require Export
  OneSortedAddition OneSortedZero OneSortedNegation
  OneSortedMultiplication OneSortedOne
  TwoSortedRightAction.
From Maniunfold.Is Require Export
  OneSortedRing OneSortedAbelianGroup
  TwoSortedRightLeftDistributive TwoSortedRightCompatible
  TwoSortedRightUnital TwoSortedRightRightDistributive.

(** Module over a noncommutative ring; right chirality.
    See [Is.TwoSortedLeftModule]. *)

Class IsRMod (A B : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasRAct A B) : Prop := {
  A_add_zero_neg_mul_one_is_ring :> IsRing add zero neg mul one;
  B_add_zero_neg_is_ab_grp :> IsAbGrp add zero neg;
  A_B_add_add_r_act_is_two_r_l_distr :> IsTwoRLDistr add add r_act;
  A_B_mul_r_act_is_r_compat :> IsRCompat mul r_act;
  A_B_zero_r_act_is_two_r_unl :> IsTwoRUnl r_act zero;
  A_B_add_r_act_is_two_r_r_distr :> IsTwoRRDistr add r_act;
}.
