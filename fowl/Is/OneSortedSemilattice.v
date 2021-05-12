(* bad *)
From Maniunfold.Has Require Export
  OneSortedBinaryOperation.
From Maniunfold.Is Require Export
  OneSortedCommutative OneSortedIdempotent OneSortedSemigroup.

Class IsSlat (A : Type)
  `(HasBinOp A) : Prop := {
  A_bin_op_is_comm :> IsComm (bin_op (A := A));
  A_bin_op_is_idem :> IsIdem (bin_op (A := A));
  A_bin_op_is_sgrp :> IsSgrp (bin_op (A := A));
}.
