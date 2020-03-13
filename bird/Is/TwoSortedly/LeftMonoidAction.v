From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit LeftAction.
From Maniunfold.Is Require Export
  Monoid LeftSemigroupAction TwoSortedly.LeftUnital.

Class IsLMonAct {A B : Type}
  (has_bin_op : HasBinOp A) (has_un : HasUn A)
  (has_l_act : HasLAct A B) : Prop := {
  bin_op_un_is_mon :> IsMon (A := A) bin_op un;
  bin_op_l_act_is_l_sgrp_act :> IsLSgrpAct bin_op l_act;
  un_l_act_is_two_l_unl :> IsTwoLUnl un l_act;
}.
