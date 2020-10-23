From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.Is Require Export
  OneSorted.LeftCancellative OneSorted.RightCancellative.

Class IsCancel (A : Type) `(HasBinOp A) : Prop := {
  A_bin_op_is_l_cancel :> IsLCancel A bin_op;
  A_bin_op_is_r_cancel :> IsRCancel A bin_op;
}.
