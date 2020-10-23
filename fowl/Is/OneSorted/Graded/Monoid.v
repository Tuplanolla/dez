From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.Graded.BinaryOperation OneSorted.Graded.NullaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Monoid OneSorted.Graded.Semigroup OneSorted.Graded.Unital.

Class IsGrdMon {A : Type} (P : A -> Type)
  `{HasBinOp A} `{HasNullOp A}
  `(HasGrdBinOp A P)
  `(HasGrdNullOp A P) : Prop := {
  A_bin_op_null_op_is_mon :> IsMon bin_op null_op;
  P_grd_bin_op_is_grd_sgrp :> IsGrdSgrp P grd_bin_op;
  P_grd_bin_op_grd_null_op_is_grd_unl :> IsGrdUnl P grd_bin_op grd_null_op;
}.
