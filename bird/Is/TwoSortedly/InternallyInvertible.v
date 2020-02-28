From Maniunfold.Has Require Export
  BinaryRelation InternalBinaryFunction Unit UnaryOperation.
From Maniunfold.Is Require Export
  LeftInternallyInvertible RightInternallyInvertible.

(** TODO Calling this "internal" is suspect,
    because it is strictly more general than "external". *)

Class IsIntInv {A B : Type} {has_bin_rel : HasBinRel B}
  (has_int_bin_fn : HasIntBinFn A B) (has_un : HasUn B)
  (has_un_op : HasUnOp A) : Prop := {
  int_bin_fn_un_un_op_is_l_int_inv :> IsLIntInv int_bin_fn un un_op;
  int_bin_fn_un_un_op_is_r_int_inv :> IsRIntInv int_bin_fn un un_op;
}.
