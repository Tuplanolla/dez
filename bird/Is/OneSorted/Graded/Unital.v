From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.Graded.BinaryOperation OneSorted.Graded.NullaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Graded.LeftUnital OneSorted.Graded.RightUnital.

Class IsGrdUnl {A : Type} {P : A -> Type}
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_grd_bin_op : HasGrdBinOp P)
  (P_has_grd_null_op : HasGrdNullOp P) : Prop := {
  grd_bin_op_grd_null_op_is_grd_l_unl :> IsGrdLUnl grd_bin_op grd_null_op;
  grd_bin_op_grd_null_op_is_grd_r_unl :> IsGrdRUnl grd_bin_op grd_null_op;
}.
