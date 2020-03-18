From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class IsComm {A : Type} (A_has_bin_op : HasBinOp A) : Prop :=
  comm : forall x y : A, x + y = y + x.
