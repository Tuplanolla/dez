From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit EndoFunction.
From Maniunfold.Is Require Export
  LeftInvertible RightInvertible.

Class IsInvertible {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A)
  (has_endo_fn : HasEndoFn A) : Prop := {
  bin_op_un_is_left_invertible :> IsLeftInvertible bin_op un endo_fn;
  bin_op_un_is_right_invertible :> IsRightInvertible bin_op un endo_fn;
}.
