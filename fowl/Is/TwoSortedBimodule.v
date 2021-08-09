(* good *)
From DEZ.Has Require Export
  Addition Zero Negation
  Multiplication One
  Action.
From DEZ.Is Require Export
  ThreeSortedBimodule.

Class IsTwoBimod (A B : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasActL A B) `(HasActR A B) : Prop :=
  A_A_B_add_zero_neg_mul_one_add_zero_neg_mul_one_add_zero_neg_act_l_act_r_is_three_bimod
    :> IsThreeBimod add zero neg mul one add zero neg mul one add zero neg
    (act_l (A := A) (B := B)) (act_r (A := A) (B := B)).
