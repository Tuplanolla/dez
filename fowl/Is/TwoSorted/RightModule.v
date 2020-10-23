From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.RightAction.
From Maniunfold.Is Require Export
  OneSorted.Ring OneSorted.AbelianGroup
  TwoSorted.RightLeftDistributive TwoSorted.RightCompatible
  TwoSorted.RightUnital TwoSorted.RightRightDistributive.

(** Module over a noncommutative ring; right chirality.
    See [Is.TwoSorted.LeftModule]. *)

Class IsRMod (A B : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasRAct A B) : Prop := {
  A_add_zero_neg_mul_one_is_ring :> IsRing A add zero neg mul one;
  B_add_zero_neg_is_ab_grp :> IsAbGrp B add zero neg;
  A_B_add_add_r_act_is_two_r_l_distr :> IsTwoRLDistr A B add add r_act;
  A_B_mul_r_act_is_r_compat :> IsRCompat A B mul r_act;
  A_B_zero_r_act_is_two_r_unl :> IsTwoRUnl A B r_act zero;
  A_B_add_r_act_is_two_r_r_distr :> IsTwoRRDistr A B add r_act;
}.
