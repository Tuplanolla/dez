From Maniunfold.Has Require Export
  BinaryOperation.
From Maniunfold.Is Require Export
  OneSortedAssociative OneSortedMagma.

(** Semigroup, associative magma. *)

Class IsSgrp (A : Type) `(HasBinOp A) : Prop := {
  bin_op_is_assoc :> IsAssoc (bin_op (A := A));
  bin_op_is_mag :> IsMag (bin_op (A := A));
}.
