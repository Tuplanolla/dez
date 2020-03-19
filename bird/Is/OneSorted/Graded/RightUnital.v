From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.Graded.BinaryOperation OneSorted.Graded.NullaryOperation.
From Maniunfold.Is Require Export
  OneSorted.RightUnital.
From Maniunfold.ShouldHave Require Import
  OneSorted.Graded.AdditiveNotations.

Class IsGrdRUnl {A : Type} {P : A -> Type}
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_grd_bin_op : HasGrdBinOp P)
  (P_has_grd_null_op : HasGrdNullOp P) : Prop := {
  bin_op_null_op_is_r_unl :> IsRUnl bin_op null_op;
  grd_r_unl : forall {i : A} (x : P i),
    rew r_unl i in (x G+ G0) = x;
}.
