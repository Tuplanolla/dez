From DEZ.Has Require Export
  BinaryOperation NullaryOperation
  GradedBinaryOperation GradedNullaryOperation.
From DEZ.Is Require Export
  OneSortedGradedLeftUnital OneSortedGradedRightUnital.

Class IsGrdUnl (A : Type) (P : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(HasGrdBinOp A P)
  `(HasGrdNullOp A P) : Prop := {
  grd_bin_op_grd_null_op_is_grd_unl_l :>
    IsGrdUnlL bin_op null_op grd_bin_op grd_null_op;
  grd_bin_op_grd_null_op_is_grd_unl_r :>
    IsGrdUnlR bin_op null_op grd_bin_op grd_null_op;
}.
