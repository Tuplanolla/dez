(* good *)
From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.LeftAction TwoSorted.RightAction.
From Maniunfold.Is Require Export
  ThreeSorted.Bimodule.

Class IsTwoBimod (A B : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasLAct A B) `(HasRAct A B) : Prop :=
  A_A_B_add_zero_neg_mul_one_add_zero_neg_mul_one_add_zero_neg_l_act_r_act_is_three_bimod
    :> IsThreeBimod add zero neg mul one add zero neg mul one add zero neg
    (l_act (A := A) (B := B)) (r_act (A := A) (B := B)).
