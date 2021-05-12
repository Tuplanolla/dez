From Maniunfold.Has Require Export
  OneSortedAddition OneSortedZero OneSortedMultiplication OneSortedOne.
From Maniunfold.Is Require Export
  OneSortedCommutative OneSortedSemiring.

(** Commutative semiring. *)

Class IsCommSring (A : Type)
  `(HasAdd A) `(HasZero A)
  `(HasMul A) `(HasOne A) : Prop := {
  A_add_zero_mul_one_is_sring :> IsSring add zero mul one;
  A_mul_is_comm :> IsComm mul;
}.
