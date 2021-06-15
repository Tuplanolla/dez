From Maniunfold.Has Require Export
  BinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

Class IsLCancel (A : Type) `(HasBinOp A) : Prop :=
  l_cancel : forall x y z : A, z + x = z + y -> x = y.
