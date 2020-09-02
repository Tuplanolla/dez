From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Multiplication OneSorted.One.
From Maniunfold.Is Require Export
  OneSorted.Commutative OneSorted.Semiring.

(** Commutative semiring. *)

Class IsCommSring (A : Type)
  (A_has_add : HasAdd A) (A_has_zero : HasZero A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A) : Prop := {
  A_add_zero_mul_one_is_sring :> IsSring A add zero mul one;
  A_mul_is_comm :> IsComm A mul;
}.
