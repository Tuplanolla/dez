From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation
  GradedBinaryOperation GradedNullaryOperation.
From Maniunfold.Is Require Export
  OneSortedGradedLeftUnital OneSortedGradedRightUnital.

Class IsGrdUnl (A : Type) (P : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(HasGrdBinOp A P)
  `(HasGrdNullOp A P) : Prop := {
  grd_bin_op_grd_null_op_is_grd_l_unl :>
    IsGrdLUnl bin_op null_op grd_bin_op grd_null_op;
  grd_bin_op_grd_null_op_is_grd_r_unl :>
    IsGrdRUnl bin_op null_op grd_bin_op grd_null_op;
}.
