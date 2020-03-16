From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation.
From Maniunfold.Is Require Export
  OneSortedly.Semigroup OneSortedly.Unital.

Class IsMon {A : Type}
  (has_bin_op : HasBinOp A) (has_null_op : HasNullOp A) : Prop := {
  bin_op_is_sgrp :> IsSgrp bin_op;
  bin_op_null_op_is_unl :> IsUnl bin_op null_op;
}.
