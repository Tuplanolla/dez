From Maniunfold.Has Require Export
  BinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

Class IsRCancel (A : Type) `(HasBinOp A) : Prop :=
  r_cancel : forall x y z : A, x + z = y + z -> x = y.
