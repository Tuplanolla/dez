From Maniunfold.Has Require Export
  OneSortedUnaryOperation OneSortedBinaryOperation.
From Maniunfold.Is Require Export
  OneSortedLeftBinaryCommutative OneSortedRightBinaryCommutative.

Class IsBinComm (A : Type)
  `(HasUnOp A) `(HasBinOp A) : Prop := {
  A_un_op_bin_op_is_l_bin_comm :> IsLBinComm un_op bin_op;
  A_un_op_bin_op_is_r_bin_comm :> IsRBinComm un_op bin_op;
}.
