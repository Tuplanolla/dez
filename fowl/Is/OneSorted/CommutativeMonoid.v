From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Commutative OneSorted.Monoid.

(** Commutative monoid, abelian monoid. *)

Class IsCommMon (A : Type)
  (A_has_bin_op : HasBinOp A) (A_has_null_op : HasNullOp A) : Prop := {
  A_bin_op_is_comm :> IsComm A bin_op;
  A_bin_op_null_op_is_mon :> IsMon A bin_op null_op;
}.
