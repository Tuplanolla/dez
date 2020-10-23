From Coq Require Import
  PArith.PArith.
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation TwoSorted.LeftAction.

Section Context.

Context {A : Type} `{A_has_bin_op : HasBinOp A}.

Import Pos.

Definition positive_op (n : positive) (x : A) : A :=
  iter_op bin_op n x.

Global Instance positive_A_has_l_act : HasLAct positive A := positive_op.

End Context.
