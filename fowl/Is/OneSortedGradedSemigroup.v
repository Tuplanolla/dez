(* bad *)
From Maniunfold.Has Require Export
  OneSortedBinaryOperation OneSortedGradedBinaryOperation.
From Maniunfold.Is Require Export
  OneSortedSemigroup OneSortedGradedAssociative OneSortedGradedMagma.

Class IsGrdSgrp (A : Type) (P : A -> Type)
  `(HasBinOp A) `(HasGrdBinOp A P) : Prop := {
  A_bin_op_is_sgrp :> IsSgrp (bin_op (A := A));
  grd_bin_op_is_grd_assoc :> IsGrdAssoc bin_op grd_bin_op;
  grd_bin_op_is_grd_mag :> IsGrdMag bin_op grd_bin_op;
}.
