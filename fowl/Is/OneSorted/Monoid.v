From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Semigroup OneSorted.Unital.

(** Monoid, unital semigroup. *)

Class IsMon (A : Type)
  `(HasBinOp A) `(HasNullOp A) : Prop := {
  A_bin_op_is_sgrp :> IsSgrp (bin_op (A := A));
  A_bin_op_null_op_is_unl :> IsUnl bin_op null_op;
}.
