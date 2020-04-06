(* bad *)
From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Semilattice OneSorted.Unital.

Class IsBndSlat {A : Type}
  (A_has_bin_op : HasBinOp A) (A_has_null_op : HasNullOp A) : Prop := {
  bin_op_is_slat :> IsSlat bin_op;
  bin_op_null_op_is_unl :> IsUnl bin_op null_op;
}.
