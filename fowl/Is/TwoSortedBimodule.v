(* good *)
From Maniunfold.Has Require Export
  OneSortedAddition OneSortedZero OneSortedNegation
  OneSortedMultiplication OneSortedOne
  TwoSortedLeftAction TwoSortedRightAction.
From Maniunfold.Is Require Export
  ThreeSortedBimodule.

Class IsTwoBimod (A B : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasLAct A B) `(HasRAct A B) : Prop :=
  A_A_B_add_zero_neg_mul_one_add_zero_neg_mul_one_add_zero_neg_l_act_r_act_is_three_bimod
    :> IsThreeBimod add zero neg mul one add zero neg mul one add zero neg
    (l_act (A := A) (B := B)) (r_act (A := A) (B := B)).
