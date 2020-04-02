From Maniunfold.Has Require Export
  OneSorted.Negation OneSorted.Multiplication.
From Maniunfold.Is Require Export
  TwoSorted.RightBinaryCommutative.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsRBinComm {A : Type}
  (A_has_neg : HasNeg A) (A_has_mul : HasMul A) : Prop :=
  r_bin_comm : forall x y : A, - (x * y) = x * - y.

Section Context.

Context {A : Type} `{A_is_r_bin_comm : IsRBinComm A}.

Global Instance A_A_neg_mul_is_two_r_bin_comm : IsTwoRBinComm A A neg mul.
Proof. intros x y. apply r_bin_comm. Qed.

End Context.
