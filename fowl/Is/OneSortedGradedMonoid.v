From Maniunfold.Has Require Export
  OneSortedBinaryOperation OneSortedNullaryOperation
  OneSortedGradedBinaryOperation OneSortedGradedNullaryOperation.
From Maniunfold.Is Require Export
  OneSortedMonoid OneSortedGradedSemigroup OneSortedGradedUnital.

Class IsGrdMon (A : Type) (P : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(HasGrdBinOp A P)
  `(HasGrdNullOp A P) : Prop := {
  bin_op_null_op_is_mon :> IsMon bin_op null_op;
  grd_bin_op_is_grd_sgrp :> IsGrdSgrp bin_op grd_bin_op;
  grd_bin_op_grd_null_op_is_grd_unl :>
    IsGrdUnl bin_op null_op grd_bin_op grd_null_op;
}.
