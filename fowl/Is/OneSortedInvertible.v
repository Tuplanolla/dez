From Maniunfold.Has Require Export
  BinaryOperation OneSortedNullaryOperation
  OneSortedUnaryOperation.
From Maniunfold.Is Require Export
  OneSortedLeftInvertible OneSortedRightInvertible.

(** Invertible. *)

Class IsInv (A : Type) `(HasBinOp A)
  `(HasNullOp A) `(HasUnOp A) : Prop := {
  A_bin_op_null_op_un_op_is_l_inv :> IsLInv bin_op null_op un_op;
  A_bin_op_null_op_un_op_is_r_inv :> IsRInv bin_op null_op un_op;
}.
