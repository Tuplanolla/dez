From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Associative OneSorted.Magma.

(** Semigroup, associative magma. *)

Class IsSgrp (A : Type) `(HasBinOp A) : Prop := {
  bin_op_is_assoc :> IsAssoc (bin_op (A := A));
  bin_op_is_mag :> IsMag (bin_op (A := A));
}.
