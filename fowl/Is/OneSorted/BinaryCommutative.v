From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.BinaryOperation.
From Maniunfold.Is Require Export
  OneSorted.LeftBinaryCommutative OneSorted.RightBinaryCommutative.

Class IsBinComm (A : Type)
  (A_has_un_op : HasUnOp A) (A_has_bin_op : HasBinOp A) : Prop := {
  A_un_op_bin_op_is_l_bin_comm :> IsLBinComm A un_op bin_op;
  A_un_op_bin_op_is_r_bin_comm :> IsRBinComm A un_op bin_op;
}.