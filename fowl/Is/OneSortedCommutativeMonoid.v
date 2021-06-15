From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation.
From Maniunfold.Is Require Export
  OneSortedCommutative OneSortedMonoid.

(** Commutative monoid, abelian monoid. *)

Class IsCommMon (A : Type)
  `(HasBinOp A) `(HasNullOp A) : Prop := {
  A_bin_op_is_comm :> IsComm (bin_op (A := A));
  A_bin_op_null_op_is_mon :> IsMon bin_op null_op;
}.
