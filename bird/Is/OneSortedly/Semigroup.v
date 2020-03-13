From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  Associative Magma.

Class IsSgrp {A : Type} (has_bin_op : HasBinOp A) : Prop := {
  bin_op_is_assoc :> IsAssoc bin_op;
  bin_op_is_mag :> IsMag bin_op;
}.
