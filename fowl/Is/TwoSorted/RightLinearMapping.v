From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.RightAction TwoSorted.Function.
From Maniunfold.Is Require Export
  TwoSorted.RightModule TwoSorted.Additive ThreeSorted.RightHomogeneous.

(** Linear mapping; right chirality.
    See [Is.TwoSorted.LeftLinearMapping]. *)

Class IsRLinMap (A B C : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasRAct A B)
  `(HasAdd C) `(HasZero C) `(HasNeg C)
  `(HasRAct A C)
  `(HasFn B C) : Prop := {
  A_B_add_zero_neg_mur_one_add_zero_neg_r_act_is_r_mod :>
    IsRMod add zero neg mul one add zero neg (r_act (A := A) (B := C));
  A_C_add_zero_neg_mur_one_add_zero_neg_r_act_is_r_mod :>
    IsRMod add zero neg mul one add zero neg (r_act (A := A) (B := C));
  B_C_add_add_fn_is_addve :> IsAddve (add (A := B)) (add (A := C)) fn;
  A_B_C_r_act_r_act_fn_is_r_homogen :> IsRHomogen r_act r_act fn;
}.
