(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Associative OneSorted.Magma.

Class IsSgrp {A : Type} (A_has_bin_op : HasBinOp A) : Prop := {
  bin_op_is_assoc :> IsAssoc bin_op;
  bin_op_is_mag :> IsMag bin_op;
}.
