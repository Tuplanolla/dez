From Maniunfold.Has Require Export
  OneSortedAddition OneSortedZero OneSortedNegation
  OneSortedMultiplication OneSortedOne
  Action.
From Maniunfold.Is Require Export
  TwoSortedRightModule TwoSortedAdditive ThreeSortedRightHomogeneous.

(** Linear mapping; right chirality.
    See [Is.TwoSortedLeftLinearMapping]. *)

Class IsRLinMap (A B C : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasActR A B)
  `(HasAdd C) `(HasZero C) `(HasNeg C)
  `(HasActR A C)
  (f : B -> C) : Prop := {
  A_B_add_zero_neg_mur_one_add_zero_neg_act_r_is_r_mod :>
    IsRMod add zero neg mul one add zero neg (act_r (A := A) (B := C));
  A_C_add_zero_neg_mur_one_add_zero_neg_act_r_is_r_mod :>
    IsRMod add zero neg mul one add zero neg (act_r (A := A) (B := C));
  B_C_add_add_fn_is_addve :> IsAddve (add (A := B)) (add (A := C)) f;
  A_B_C_act_r_act_r_fn_is_r_homogen :> IsRHomogen act_r act_r f;
}.
