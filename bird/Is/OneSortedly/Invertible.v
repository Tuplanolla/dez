From Maniunfold.Has.OneSorted Require Export
  BinaryOperation NullaryOperation UnaryOperation.
From Maniunfold.Is.OneSortedly Require Export
  LeftInvertible RightInvertible.

Class IsInv {A : Type} (has_bin_op : HasBinOp A)
  (has_null_op : HasNullOp A) (has_un_op : HasUnOp A) : Prop := {
  bin_op_null_op_un_op_is_l_inv :> IsLInv bin_op null_op un_op;
  bin_op_null_op_un_op_is_r_inv :> IsRInv bin_op null_op un_op;
}.
