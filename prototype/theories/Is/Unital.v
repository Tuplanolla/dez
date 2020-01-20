From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit.
From Maniunfold.Is Require Export
  LeftUnital RightUnital.

Class IsUn {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop := {
  bin_op_un_is_left_unital :> IsLUn bin_op un;
  bin_op_un_is_right_unital :> IsRUn bin_op un;
}.
