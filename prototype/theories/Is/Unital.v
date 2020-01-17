From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit.
From Maniunfold.Is Require Export
  LeftUnital RightUnital.

Class IsUnital {A : Type} {has_eq_rel : HasEqRel A}
  (has_bi_op : HasBiOp A) (has_un : HasUn A) : Prop := {
  bi_op_un_is_left_unital :> IsLeftUnital bi_op un;
  bi_op_un_is_right_unital :> IsRightUnital bi_op un;
}.
