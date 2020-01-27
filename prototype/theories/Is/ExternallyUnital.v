From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit.
From Maniunfold.Is Require Export
  LeftExternallyUnital RightExternallyUnital.

Class IsExtUnl {A : Type} {has_bin_rel : HasBinRel A}
  (has_bin_op : HasBinOp A)
  (has_l_un : HasLUn A) (has_r_un : HasRUn A) : Prop := {
  bin_op_l_un_is_l_ext_unl :> IsLExtUnl bin_op l_un;
  bin_op_r_un_is_r_ext_unl :> IsRExtUnl bin_op r_un;
}.
