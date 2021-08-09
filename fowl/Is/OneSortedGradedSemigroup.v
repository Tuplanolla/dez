(* bad *)
From DEZ.Has Require Export
  BinaryOperation GradedBinaryOperation.
From DEZ.Is Require Export
  Semigroup GradedAssociative OneSortedGradedMagma.

Class IsGrdSemigrp (A : Type) (P : A -> Type)
  `(HasBinOp A) `(HasGrdBinOp A P) : Prop := {
  A_bin_op_is_semigrp :> IsSemigrp (bin_op (A := A));
  grd_bin_op_is_grd_assoc :> IsGrdAssoc bin_op grd_bin_op;
  grd_bin_op_is_grd_mag :> IsGrdMag bin_op grd_bin_op;
}.
