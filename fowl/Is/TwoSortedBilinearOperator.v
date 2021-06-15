From Maniunfold.Has Require Export
  OneSortedAddition OneSortedZero OneSortedNegation
  OneSortedMultiplication OneSortedOne
  Action Action.
From Maniunfold.Is Require Export
  FiveSortedBilinearMapping.

(** Bilinear operator on a bimodule over a noncommutative ring.
    The scalars are carried by [A] and the vectors by [B].
    We refer to the operator as multiplication,
    so that it does not get mixed up with addition,
    since they both have the same type and same superclasses. *)

Class IsBilinOp (A B : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasActL A B) `(HasActR A B)
  `(HasMul B) : Prop :=
  A_A_B_B_B_add_zero_neg_mul_one_add_zero_neg_mul_one_add_zero_neg_add_zero_neg_add_zero_neg_act_l_act_r_act_l_act_r_mul_is_bilin_map
    :> IsBilinMap add zero neg mul one add zero neg mul one
    add zero neg add zero neg add zero neg act_l act_r act_l act_r mul.
