From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Semigroup OneSorted.Unital.

Class IsMon {A : Type}
  (A_has_bin_op : HasBinOp A) (A_has_null_op : HasNullOp A) : Prop := {
  bin_op_is_sgrp :> IsSgrp bin_op;
  bin_op_null_op_is_unl :> IsUnl bin_op null_op;
}.
