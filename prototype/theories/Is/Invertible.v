From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit UnaryOperation.
From Maniunfold.Is Require Export
  LeftInvertible RightInvertible.

Class IsInv {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A)
  (has_un_op : HasUnOp A) : Prop := {
  bin_op_un_is_left_invertible :> IsLInv bin_op un un_op;
  bin_op_un_is_right_invertible :> IsRInv bin_op un un_op;
}.
