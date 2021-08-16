From DEZ.Has Require Export
  BinaryOperation NullaryOperation.
From DEZ.Is Require Export
  Commutative Monoid.

(** Commutative monoid, abelian monoid. *)

Class IsCommMon (A : Type)
  `(HasBinOp A) `(HasNullOp A) : Prop := {
  A_bin_op_is_comm :> IsComm (bin_op (A := A));
  A_bin_op_null_op_is_mon :> IsMon null_op bin_op;
}.
