From Maniunfold.Has Require Export
  OneSorted.BinaryOperation
  TwoSorted.LeftAction TwoSorted.LeftTorsion.
From Maniunfold.Is Require Export
  TwoSorted.LeftMagmaAction TwoSorted.LeftUnique.

Class IsLMagTor (A B : Type)
  (A_has_bin_op : HasBinOp A)
  (A_B_has_l_act : HasLAct A B) (A_B_has_l_tor : HasLTor A B) : Prop := {
  bin_op_l_act_is_l_mag_act :> IsLMagAct A B bin_op l_act;
  l_act_l_tor_l_uniq :> IsLUniq A B l_act l_tor;
}.
