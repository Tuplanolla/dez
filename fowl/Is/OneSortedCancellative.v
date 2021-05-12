From Maniunfold.Has Require Export
  OneSortedBinaryOperation.
From Maniunfold.Is Require Export
  OneSortedLeftCancellative OneSortedRightCancellative.

Class IsCancel (A : Type) `(HasBinOp A) : Prop := {
  A_bin_op_is_l_cancel :> IsLCancel (bin_op (A := A));
  A_bin_op_is_r_cancel :> IsRCancel (bin_op (A := A));
}.
