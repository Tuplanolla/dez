(* bad *)
From Maniunfold.Has Require Export
  Negation Multiplication.
From Maniunfold.Is Require Export
  TwoSortedLeftBinaryCommutative.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations.

Class IsLBinComm (A : Type) `(HasNeg A) `(HasMul A) : Prop :=
  l_bin_comm : forall x y : A, - (x * y) = x * - y.

Section Context.

Context (A : Type) `{IsLBinComm A}.

Global Instance A_A_neg_mul_is_two_l_bin_comm : IsTwoLBinComm neg mul.
Proof. intros x y. apply l_bin_comm. Defined.

End Context.
