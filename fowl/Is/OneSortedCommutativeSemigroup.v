From Maniunfold.Has Require Export
  BinaryOperation.
From Maniunfold.Is Require Export
  OneSortedCommutative OneSortedSemigroup.

(** Commutative semigroup, abelian semigroup. *)

Class IsCommSgrp (A : Type) `(HasBinOp A) : Prop := {
  A_bin_op_is_comm :> IsComm (bin_op (A := A));
  A_bin_op_is_sgrp :> IsSgrp (bin_op (A := A));
}.
