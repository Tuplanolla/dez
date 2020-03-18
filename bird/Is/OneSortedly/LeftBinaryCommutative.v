From Maniunfold.Has Require Export
  EquivalenceRelation Negation Multiplication.
From Maniunfold.Is Require Import
  LeftExternallyBinaryCommutative.
From Maniunfold.ShouldHave Require Import
  ArithmeticNotations.

Class IsLBinComm {A : Type}
  (has_neg : HasNeg A) (has_mul : HasMul A) : Prop :=
  l_bin_comm : forall x y : A, - (x * y) = - x * y.

Section Context.

Context {A : Type} `{is_l_bin_comm : IsLBinComm A}.

Global Instance neg_mul_is_l_ext_bin_comm : IsLExtBinComm neg mul.
Proof. intros x y. apply l_bin_comm. Qed.

End Context.
