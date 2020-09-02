From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Associative OneSorted.Magma.

(** Semigroup, associative magma. *)

Class IsSgrp (A : Type) (A_has_bin_op : HasBinOp A) : Prop := {
  A_bin_op_is_assoc :> IsAssoc A bin_op;
  A_bin_op_is_mag :> IsMag A bin_op;
}.
