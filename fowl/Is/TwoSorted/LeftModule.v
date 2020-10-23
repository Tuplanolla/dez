From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.LeftAction.
From Maniunfold.Is Require Export
  OneSorted.Ring OneSorted.AbelianGroup
  TwoSorted.LeftRightDistributive TwoSorted.LeftCompatible
  TwoSorted.LeftUnital TwoSorted.LeftLeftDistributive.

(** Module over a noncommutative ring; left chirality.
    The ring is carried by [A] and the module by [B]. *)

Class IsLMod (A B : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasLAct A B) : Prop := {
  A_add_zero_neg_mul_one_is_ring :> IsRing A add zero neg mul one;
  B_add_zero_neg_is_ab_grp :> IsAbGrp B add zero neg;
  A_B_add_add_l_act_is_two_l_r_distr :> IsTwoLRDistr A B add add l_act;
  A_B_mul_l_act_is_l_compat :> IsLCompat A B mul l_act;
  A_B_zero_l_act_is_two_l_unl :> IsTwoLUnl A B l_act zero;
  A_B_add_l_act_is_two_l_l_distr :> IsTwoLLDistr A B add l_act;
}.
