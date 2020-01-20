From Coq Require Import
  PArith.
From Maniunfold.Has Require Export
  BinaryOperation.

Import Pos.

Definition p_op {A : Type} {has_bin_op : HasBinOp A}
  (n : positive) (x : A) : A :=
  iter_op bin_op n x.
