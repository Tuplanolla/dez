From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.LeftAction TwoSorted.Function.
From Maniunfold.Is Require Export
  TwoSorted.LeftModule TwoSorted.Additive ThreeSorted.LeftHomogeneous.

(** Linear mapping, homomorphism between two modules,
    where both modules are defined over a noncommutative ring; left chirality.
    The ring is carried by [A] the modules by [B] and [C]. *)

Class IsLLinMap (A B C : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasLAct A B)
  `(HasAdd C) `(HasZero C) `(HasNeg C)
  `(HasLAct A C)
  `(HasFn B C) : Prop := {
  A_B_add_zero_neg_mul_one_add_zero_neg_l_act_is_l_mod :>
    IsLMod A B add zero neg mul one add zero neg l_act;
  A_C_add_zero_neg_mul_one_add_zero_neg_l_act_is_l_mod :>
    IsLMod A C add zero neg mul one add zero neg l_act;
  B_C_add_add_fn_is_addve :> IsAddve B C add add fn;
  A_B_C_l_act_l_act_fn_is_l_homogen :> IsLHomogen A B C l_act l_act fn;
}.
