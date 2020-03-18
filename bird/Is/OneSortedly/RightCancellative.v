From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class IsRCancel {A : Type}
  (has_bin_op : HasBinOp A) : Prop :=
  r_cancel : forall x y z : A, x + z = y + z -> x = y.
