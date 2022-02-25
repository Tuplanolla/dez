(* bad *)
From DEZ.Has Require Export
  Negation Multiplication.
From DEZ.Is Require Export
  TwoSortedRightBinaryCommutative.
From DEZ.Supports Require Import
  OneSortedArithmeticNotations.

Class IsRBinComm (A : Type)
  `(HasNeg A) `(HasMul A) : Prop :=
  r_bin_comm : forall x y : A, - (x * y) = - x * y.

Section Context.

Context (A : Type) `{IsRBinComm A}.

Global Instance A_A_neg_mul_is_two_r_bin_comm : IsTwoRBinComm neg mul.
Proof. intros x y. apply r_bin_comm. Defined.

End Context.
