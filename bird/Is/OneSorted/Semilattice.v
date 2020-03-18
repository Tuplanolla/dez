From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Commutative OneSorted.Idempotent OneSorted.Semigroup.

Class IsSlat {A : Type}
  (A_has_bin_op : HasBinOp A) : Prop := {
  bin_op_is_comm :> IsComm bin_op;
  bin_op_is_idem :> IsIdem bin_op;
  bin_op_is_sgrp :> IsSgrp bin_op;
}.
