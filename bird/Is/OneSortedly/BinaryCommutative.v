From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation UnaryOperation.
From Maniunfold.Is Require Export
  LeftBinaryCommutative RightBinaryCommutative.

(** TODO This is nonsense and should be called some sort of distributivity. *)

Class IsBinComm {A : Type}
  (has_un_op : HasUnOp A) (has_bin_op : HasBinOp A) : Prop := {
  un_op_bin_op_is_l_bin_comm :> IsLBinComm un_op bin_op;
  un_op_bin_op_is_r_bin_comm :> IsRBinComm un_op bin_op;
}.
