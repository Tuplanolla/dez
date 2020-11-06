(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.Graded.BinaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Semigroup OneSorted.Graded.Associative OneSorted.Graded.Magma.

Class IsGrdSgrp (A : Type) (P : A -> Type)
  `(HasBinOp A) `(HasGrdBinOp A P) : Prop := {
  A_bin_op_is_sgrp :> IsSgrp (bin_op (A := A));
  P_grd_bin_op_is_grd_assoc :> IsGrdAssoc P bin_op grd_bin_op;
  P_grd_bin_op_is_grd_mag :> IsGrdMag P bin_op grd_bin_op;
}.
