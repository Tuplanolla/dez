From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.UnaryOperation.
From Maniunfold.Is Require Export
  OneSorted.LeftInvertible OneSorted.RightInvertible.

(** Invertible. *)

Class IsInv (A : Type) `(HasBinOp A)
  `(HasNullOp A) `(HasUnOp A) : Prop := {
  A_bin_op_null_op_un_op_is_l_inv :> IsLInv A bin_op null_op un_op;
  A_bin_op_null_op_un_op_is_r_inv :> IsRInv A bin_op null_op un_op;
}.
