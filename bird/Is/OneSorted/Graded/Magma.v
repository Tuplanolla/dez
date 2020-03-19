From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.Graded.BinaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Magma.

Class IsGrdMag {A : Type} {P : A -> Type}
  (A_has_bin_op : HasBinOp A) (P_has_grd_bin_op : HasGrdBinOp P) : Prop := {
  bin_op_is_mag :> IsMag bin_op;
}.
