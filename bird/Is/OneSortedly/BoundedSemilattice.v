From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  OneSortedly.Semilattice OneSortedly.Unital.

Class IsBndSlat {A : Type}
  (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop := {
  bin_op_is_slat :> IsSlat bin_op;
  bin_op_un_is_unl :> IsUnl bin_op un;
}.
