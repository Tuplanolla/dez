From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation
  LeftAction LeftTorsion.
From Maniunfold.Is Require Export
  Magma LeftGroupAction LeftUnique.

Class IsLMagTor {A B : Type}
  (has_bin_op : HasBinOp A)
  (has_l_act : HasLAct A B) (has_l_tor : HasLTor A B) : Prop := {
  bin_op_l_act_is_l_mag_act :> IsLMagAct bin_op l_act;
  l_act_l_tor_left_uniq :> IsLNullOpiq l_act l_tor;
}.
