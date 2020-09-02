From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class IsLCancel (A : Type) (A_has_bin_op : HasBinOp A) : Prop :=
  l_cancel : forall x y z : A, z + x = z + y -> x = y.
