From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class IsLCancel {A : Type}
  (has_bin_op : HasBinOp A) : Prop :=
  l_cancel : forall x y z : A, z + x = z + y -> x = y.
