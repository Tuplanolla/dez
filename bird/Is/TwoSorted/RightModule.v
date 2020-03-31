From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation OneSorted.Multiplication
  OneSorted.One TwoSorted.RightAction.
From Maniunfold.Is Require Export
  OneSorted.Ring OneSorted.AbelianGroup TwoSorted.RightLeftDistributive
  TwoSorted.RightCompatible TwoSorted.RightUnital
  TwoSorted.RightRightDistributive.

Class IsRMod {A B : Type}
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (A_B_has_r_act : HasRAct A B) : Prop := {
  add_zero_neg_mul_one_is_ring :> IsRing (A := A) add zero neg mul one;
  add_zero_neg_is_ab_grp :> IsAbGrp (A := B) add zero neg;
  add_add_r_act_is_two_r_l_distr :>
    IsTwoRLDistr (A := A) (B := B) add add r_act;
  mul_r_act_is_r_compat :> IsRCompat (A := A) (B := B) mul r_act;
  zero_r_act_is_two_r_unl :> IsTwoRUnl (A := A) (B := B) zero r_act;
  add_r_act_is_two_r_r_distr :> IsTwoRRDistr (A := A) (B := B) add r_act;
}.
