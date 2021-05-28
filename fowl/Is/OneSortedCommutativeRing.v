From Maniunfold.Has Require Export
  OneSortedAddition OneSortedZero OneSortedNegation
  OneSortedMultiplication OneSortedOne.
From Maniunfold.Is Require Export
  OneSortedRing OneSortedCommutative.

(** Commutative ring. *)

Class IsCommRing (A : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A) : Prop := {
  A_add_zero_neg_mul_one_is_ring :> IsRing add zero neg mul one;
  A_mul_is_comm :> IsComm mul;
}.