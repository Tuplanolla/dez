From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  LeftCancellative RightCancellative.

Class IsCancel {A : Type}
  (has_bin_op : HasBinOp A) : Prop := {
  bin_op_is_l_reg :> IsLCancel bin_op;
  bin_op_is_r_reg :> IsRCancel bin_op;
}.
