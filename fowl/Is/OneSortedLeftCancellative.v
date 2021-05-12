From Maniunfold.Has Require Export
  OneSortedBinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

Class IsLCancel (A : Type) `(HasBinOp A) : Prop :=
  l_cancel : forall x y z : A, z + x = z + y -> x = y.
