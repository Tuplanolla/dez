From Coq Require Import
  ZArith.
From Maniunfold.Has Require Export
  BinaryOperation.

Import Pos.

Definition pop {A : Type} {has_bin_op : HasBinOp A} (n : positive) (x : A) : A :=
  iter_op bin_op n x.
