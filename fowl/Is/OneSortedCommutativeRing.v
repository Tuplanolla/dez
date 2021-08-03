From Maniunfold.Has Require Export
  Addition Zero Negation
  Multiplication One.
From Maniunfold.Is Require Export
  Ring Commutative.

(** Commutative ring. *)

Class IsCommRing (A : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A) : Prop := {
  A_add_zero_neg_mul_one_is_ring :> IsRing zero neg add one mul;
  A_mul_is_comm :> IsCommBinOp mul;
}.
