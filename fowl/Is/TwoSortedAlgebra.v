From Maniunfold.Has Require Export
  OneSortedAddition OneSortedZero OneSortedNegation
  OneSortedMultiplication OneSortedOne
  Action Action.
From Maniunfold.Is Require Export
  OneSortedRing TwoSortedBimodule TwoSortedBilinearOperator.

(** Noncommutative nonunital nonassociative algebra over a noncommutative ring.
    The ring is carried by [A] and the algebra by [B].
    Informally, this is the magma of algebralike structures. *)

Class IsAlg (A B : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasMul B)
  `(HasActL A B) `(HasActR A B) : Prop := {
  A_add_zero_neg_mul_one_is_ring :> IsRing add zero neg mul one;
  A_B_add_zero_neg_mul_one_add_zero_neg_act_l_act_r_is_two_bimod :>
    IsTwoBimod add zero neg mul one add zero neg (act_l (A := A) (B := B)) act_r;
  A_B_add_zero_neg_mul_one_add_zero_neg_mul_act_l_act_r_is_bilin_op :>
    IsBilinOp add zero neg mul one add zero neg (act_l (A := A) (B := B)) act_r mul;
}.
