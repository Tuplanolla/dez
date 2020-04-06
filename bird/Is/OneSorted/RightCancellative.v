(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class IsRCancel {A : Type} (A_has_bin_op : HasBinOp A) : Prop :=
  r_cancel : forall x y z : A, x + z = y + z -> x = y.
