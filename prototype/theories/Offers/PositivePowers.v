From Coq Require Import
  ZArith.
From Maniunfold.Has Require Export
  BinaryOperation.

Import Pos.

Definition pop {A : Type} {has_bi_op : HasBinOp A} (n : positive) (x : A) : A :=
  iter_op bi_op n x.
