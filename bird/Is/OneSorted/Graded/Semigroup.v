From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.Graded.BinaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Semigroup OneSorted.Graded.Associative OneSorted.Graded.Magma.

Class IsGrdSgrp {A : Type} {P : A -> Type}
  {A_has_bin_op : HasBinOp A} (P_has_grd_bin_op : HasGrdBinOp P) : Prop := {
  bin_op_is_sgrp :> IsSgrp bin_op;
  grd_bin_op_is_grd_assoc :> IsGrdAssoc grd_bin_op;
  grd_bin_op_is_grd_mag :> IsGrdMag grd_bin_op;
}.
