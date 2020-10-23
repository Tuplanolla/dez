(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Semilattice OneSorted.Unital.

Class IsBndSlat (A : Type)
  `(HasBinOp A) `(HasNullOp A) : Prop := {
  A_bin_op_is_slat :> IsSlat (bin_op (A := A));
  A_bin_op_null_op_is_unl :> IsUnl bin_op null_op;
}.
