From Maniunfold.Has.OneSorted Require Export
  Addition Zero Negation Multiplication One.
From Maniunfold.Is.OneSortedly Require Export
  Ring Commutative.

(** This is a unital commutative ring. *)

Class IsCommRing {A : Type}
  (has_add : HasAdd A) (has_zero : HasZero A) (has_neg : HasNeg A)
  (has_mul : HasMul A) (has_one : HasOne A) : Prop := {
  add_zero_neg_mul_one_is_ring :> IsRing add zero neg mul one;
  mul_is_comm :> IsComm mul;
}.
