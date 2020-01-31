From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  Magma Associative.

Class IsSgrp {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) : Prop := {
  bin_op_is_mag :> IsMag bin_op;
  bin_op_is_assoc :> IsAssoc bin_op;
}.
