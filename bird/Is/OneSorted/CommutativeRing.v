(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One.
From Maniunfold.Is Require Export
  OneSorted.Ring OneSorted.Commutative.

(** This is a unital commutative ring. *)

Class IsCommRing {A : Type}
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A) : Prop := {
  add_zero_neg_mul_one_is_ring :> IsRing add zero neg mul one;
  mul_is_comm :> IsComm mul;
}.
