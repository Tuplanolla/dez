From Maniunfold.Has.OneSorted Require Export
  BinaryOperation.
From Maniunfold.ShouldHave.OneSorted Require Import
  AdditiveNotations.

Class IsComm {A : Type} (has_bin_op : HasBinOp A) : Prop :=
  comm : forall x y : A, x + y = y + x.
