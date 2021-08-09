From DEZ.Has Require Export
  BinaryOperation NullaryOperation
  GradedBinaryOperation GradedNullaryOperation.
From DEZ.Is Require Export
  Monoid OneSortedGradedSemigroup OneSortedGradedUnital.

Class IsGrdMon (A : Type) (P : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(HasGrdBinOp A P)
  `(HasGrdNullOp A P) : Prop := {
  bin_op_null_op_is_mon :> IsMon null_op bin_op;
  grd_bin_op_is_grd_semigrp :> IsGrdSemigrp bin_op grd_bin_op;
  grd_bin_op_grd_null_op_is_grd_unl :>
    IsGrdUnl bin_op null_op grd_bin_op grd_null_op;
}.
