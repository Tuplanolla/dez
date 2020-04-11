(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Negation OneSorted.Multiplication.
From Maniunfold.Is Require Export
  TwoSorted.LeftBinaryCommutative.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsLBinComm (A : Type)
  (A_has_neg : HasNeg A) (A_has_mul : HasMul A) : Prop :=
  l_bin_comm : forall x y : A, - (x * y) = x * - y.

Section Context.

Context {A : Type} `{is_l_bin_comm : IsLBinComm A}.

Global Instance A_A_neg_mul_is_two_l_bin_comm : IsTwoLBinComm A A neg mul.
Proof. intros x y. apply l_bin_comm. Defined.

End Context.
