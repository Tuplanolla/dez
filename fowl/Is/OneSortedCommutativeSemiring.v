From Maniunfold.Has Require Export
  Addition Zero Multiplication One.
From Maniunfold.Is Require Export
  OneSortedCommutative OneSortedSemiring.

(** Commutative semiring. *)

Class IsCommSemiring (A : Type)
  `(HasAdd A) `(HasZero A)
  `(HasMul A) `(HasOne A) : Prop := {
  A_add_zero_mul_one_is_sring :> IsSemiring add zero mul one;
  A_mul_is_comm :> IsComm mul;
}.
