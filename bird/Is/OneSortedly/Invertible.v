From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit UnaryOperation.
From Maniunfold.Is Require Export
  LeftInvertible RightInvertible.

Class IsInv {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A)
  (has_un_op : HasUnOp A) : Prop := {
  bin_op_un_un_op_is_l_inv :> IsLInv bin_op un un_op;
  bin_op_un_un_op_is_r_inv :> IsRInv bin_op un un_op;
}.
