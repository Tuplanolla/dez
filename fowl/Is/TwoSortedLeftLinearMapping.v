From Maniunfold.Has Require Export
  OneSortedAddition OneSortedZero OneSortedNegation
  OneSortedMultiplication OneSortedOne
  Action.
From Maniunfold.Is Require Export
  TwoSortedLeftModule TwoSortedAdditive ThreeSortedLeftHomogeneous.

(** Linear mapping, homomorphism between two modules,
    where both modules are defined over a noncommutative ring; left chirality.
    The ring is carried by [A] the modules by [B] and [C]. *)

Class IsLLinMap (A B C : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasActL A B)
  `(HasAdd C) `(HasZero C) `(HasNeg C)
  `(HasActL A C)
  (f : B -> C) : Prop := {
  A_B_add_zero_neg_mul_one_add_zero_neg_act_l_is_l_mod :>
    IsLMod add zero neg mul one add zero neg (act_l (A := A) (B := B));
  A_C_add_zero_neg_mul_one_add_zero_neg_act_l_is_l_mod :>
    IsLMod add zero neg mul one add zero neg (act_l (A := A) (B := C));
  B_C_add_add_fn_is_addve :> IsAddve (add (A := B)) (add (A := C)) f;
  A_B_C_act_l_act_l_fn_is_l_homogen :> IsLHomogen act_l act_l f;
}.
