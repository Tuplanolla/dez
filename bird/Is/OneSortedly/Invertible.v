From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.UnaryOperation.
From Maniunfold.Is Require Export
  OneSortedly.LeftInvertible OneSortedly.RightInvertible.

Class IsInv {A : Type} (A_has_bin_op : HasBinOp A)
  (A_has_null_op : HasNullOp A) (A_has_un_op : HasUnOp A) : Prop := {
  bin_op_null_op_un_op_is_l_inv :> IsLInv bin_op null_op un_op;
  bin_op_null_op_un_op_is_r_inv :> IsRInv bin_op null_op un_op;
}.
