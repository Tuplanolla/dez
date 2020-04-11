(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Semilattice OneSorted.Unital.

Class IsBndSlat (A : Type)
  (A_has_bin_op : HasBinOp A) (A_has_null_op : HasNullOp A) : Prop := {
  A_bin_op_is_slat :> IsSlat A bin_op;
  A_bin_op_null_op_is_unl :> IsUnl A bin_op null_op;
}.
