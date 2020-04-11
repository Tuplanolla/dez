From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Semigroup OneSorted.Unital.

(** Monoid, unital semigroup. *)

Class IsMon (A : Type)
  (A_has_bin_op : HasBinOp A) (A_has_null_op : HasNullOp A) : Prop := {
  A_bin_op_is_sgrp :> IsSgrp A bin_op;
  A_bin_op_null_op_is_unl :> IsUnl A bin_op null_op;
}.
