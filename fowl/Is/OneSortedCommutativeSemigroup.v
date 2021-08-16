From DEZ.Has Require Export
  BinaryOperation.
From DEZ.Is Require Export
  Commutative Semigroup.

(** Commutative semigroup, abelian semigroup. *)

Class IsCommSemigrp (A : Type) `(HasBinOp A) : Prop := {
  A_bin_op_is_comm :> IsComm (bin_op (A := A));
  A_bin_op_is_semigrp :> IsSemigrp (bin_op (A := A));
}.
