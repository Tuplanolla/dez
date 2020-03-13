From Maniunfold.Has Require Export
  OneSorted.BinaryOperation TwoSorted.LeftAction.
From Maniunfold.Is.OneSortedly Require Export
  Magma.

Class IsLMagAct {A B : Type}
  (A_has_bin_op : HasBinOp A) (has_l_act : HasLAct A B) : Prop := {
  A_bin_op_is_mag :> IsMag (A := A) bin_op;
}.
