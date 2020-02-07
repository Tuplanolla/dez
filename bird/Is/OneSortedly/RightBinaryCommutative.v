From Maniunfold.Has Require Export
  EquivalenceRelation Negation Multiplication.
From Maniunfold.Is Require Import
  RightExternallyBinaryCommutative.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

Class IsRBinComm {A : Type} {has_eq_rel : HasEqRel A}
  (has_neg : HasNeg A) (has_mul : HasMul A) : Prop :=
  r_bin_comm : forall x y : A, - (x * y) == x * - y.

Section Context.

Context {A : Type} `{is_r_bin_comm : IsRBinComm A}.

Global Instance neg_mul_is_r_ext_bin_comm : IsRExtBinComm neg mul.
Proof. intros x y. apply r_bin_comm. Qed.

End Context.
