From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Multiplication OneSorted.One.
From Maniunfold.Is Require Export
  OneSorted.Commutative OneSorted.Semiring.

(** Commutative semiring. *)

Class IsCommSring (A : Type)
  `(HasAdd A) `(HasZero A)
  `(HasMul A) `(HasOne A) : Prop := {
  A_add_zero_mul_one_is_sring :> IsSring A add zero mul one;
  A_mul_is_comm :> IsComm A mul;
}.
