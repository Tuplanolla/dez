From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class IsIdem {A : Type}
  (has_bin_op : HasBinOp A) : Prop :=
  idem : forall x y : A, x + x = x.
