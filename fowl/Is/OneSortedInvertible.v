From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation
  UnaryOperation.
From Maniunfold.Is Require Export
  OneSortedLeftInvertible OneSortedRightInvertible.

(** Invertible. *)

Class IsInvLR (A : Type) `(HasBinOp A)
  `(HasNullOp A) `(HasUnOp A) : Prop := {
  A_bin_op_null_op_un_op_is_l_inv_hom :> IsLInv bin_op null_op un_op;
  A_bin_op_null_op_un_op_is_r_inv_hom :> IsRInv bin_op null_op un_op;
}.
