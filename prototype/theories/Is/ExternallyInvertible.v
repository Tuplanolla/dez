From Maniunfold.Has Require Export
  EquivalenceRelation InternalBinaryFunction Unit UnaryOperation.
From Maniunfold.Is Require Export
  LeftExternallyInvertible RightExternallyInvertible.

Class IsExtInv {A B : Type} {has_bin_rel : HasBinRel B}
  (has_int_bin_fn : HasIntBinFn A B) (has_un : HasUn B)
  (has_un_op : HasUnOp A) : Prop := {
  int_bin_fn_un_un_op_is_l_ext_inv :> IsLExtInv int_bin_fn un un_op;
  int_bin_fn_un_un_op_is_r_ext_inv :> IsRExtInv int_bin_fn un un_op;
}.
