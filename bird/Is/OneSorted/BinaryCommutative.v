From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.BinaryOperation.
From Maniunfold.Is Require Export
  OneSorted.LeftBinaryCommutative OneSorted.RightBinaryCommutative.

(** TODO This is nonsense and should be called some sort of distributivity. *)

Class IsBinComm {A : Type}
  (A_has_un_op : HasUnOp A) (A_has_bin_op : HasBinOp A) : Prop := {
  un_op_bin_op_is_l_bin_comm :> IsLBinComm un_op bin_op;
  un_op_bin_op_is_r_bin_comm :> IsRBinComm un_op bin_op;
}.
