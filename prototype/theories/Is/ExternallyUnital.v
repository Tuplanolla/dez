From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit.
From Maniunfold.Is Require Export
  LeftExternallyUnital RightExternallyUnital.

Class IsExtUn {A : Type} {has_bin_rel : HasBinRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop := {
  bin_op_un_is_l_ext_un :> IsLExtUn bin_op un;
  bin_op_un_is_r_ext_un :> IsRExtUn bin_op un;
}.
