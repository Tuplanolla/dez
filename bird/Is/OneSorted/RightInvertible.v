(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.UnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class IsRInv {A : Type} (A_has_bin_op : HasBinOp A)
  (A_has_null_op : HasNullOp A) (A_has_un_op : HasUnOp A) : Prop :=
  r_inv : forall x : A, x + (- x) = 0.
