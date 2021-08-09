From DEZ.Has Require Export
  Addition Zero Multiplication One.
From DEZ.Is Require Export
  Commutative Semiring.

(** Commutative semiring. *)

Class IsCommSemiring (A : Type)
  `(HasAdd A) `(HasZero A)
  `(HasMul A) `(HasOne A) : Prop := {
  A_add_zero_mul_one_is_semiring :> IsSemiring zero add one mul;
  A_mul_is_comm :> IsCommBinOp mul;
}.
