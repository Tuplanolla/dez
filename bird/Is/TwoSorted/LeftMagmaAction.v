From Maniunfold.Has Require Export
  OneSorted.BinaryOperation TwoSorted.LeftAction.
From Maniunfold.Is Require Export
  OneSorted.Magma.

Class IsLMagAct (A B : Type)
  (A_has_bin_op : HasBinOp A) (A_B_has_l_act : HasLAct A B) : Prop := {
  A_bin_op_is_mag :> IsMag (A := A) bin_op;
}.
