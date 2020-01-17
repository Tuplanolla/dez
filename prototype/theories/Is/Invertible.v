From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit EndoFunction.
From Maniunfold.Is Require Export
  LeftInvertible RightInvertible.

Class IsInvertible {A : Type} {has_eq_rel : HasEqRel A}
  (has_bi_op : HasBinOp A) (has_un : HasUn A)
  (has_endo_fn : HasEndoFn A) : Prop := {
  bi_op_un_is_left_invertible :> IsLeftInvertible bi_op un endo_fn;
  bi_op_un_is_right_invertible :> IsRightInvertible bi_op un endo_fn;
}.
