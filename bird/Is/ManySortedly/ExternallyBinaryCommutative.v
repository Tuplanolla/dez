From Maniunfold.Has Require Export
  BinaryRelation BinaryOperation UnaryOperation.
From Maniunfold.Is Require Export
  LeftExternallyBinaryCommutative RightExternallyBinaryCommutative.

(** TODO This is nonsense and should be called some sort of distributivity. *)

Class IsExtBinComm {A : Type} {has_bin_rel : HasBinRel A}
  (has_bin_op : HasBinOp A) (has_un_op : HasUnOp A) : Prop := {
  bin_op_un_op_is_l_ext_bin_comm :> IsLExtBinComm bin_op un_op;
  bin_op_un_op_is_r_ext_bin_comm :> IsRExtBinComm bin_op un_op;
}.
