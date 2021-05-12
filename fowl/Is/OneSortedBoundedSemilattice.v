(* bad *)
From Maniunfold.Has Require Export
  OneSortedBinaryOperation.
From Maniunfold.Is Require Export
  OneSortedSemilattice OneSortedUnital.

Class IsBndSlat (A : Type)
  `(HasBinOp A) `(HasNullOp A) : Prop := {
  A_bin_op_is_slat :> IsSlat (bin_op (A := A));
  A_bin_op_null_op_is_unl :> IsUnl bin_op null_op;
}.
