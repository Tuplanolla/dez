(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Commutative OneSorted.Idempotent OneSorted.Semigroup.

Class IsSlat (A : Type)
  `(HasBinOp A) : Prop := {
  A_bin_op_is_comm :> IsComm A bin_op;
  A_bin_op_is_idem :> IsIdem A bin_op;
  A_bin_op_is_sgrp :> IsSgrp A bin_op;
}.
