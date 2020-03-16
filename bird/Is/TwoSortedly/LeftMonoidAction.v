From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation NullaryOperation LeftAction.
From Maniunfold.Is Require Export
  Monoid LeftSemigroupAction TwoSortedly.LeftUnital.

Class IsLMonAct {A B : Type}
  (has_bin_op : HasBinOp A) (has_null_op : HasNullOp A)
  (has_l_act : HasLAct A B) : Prop := {
  bin_op_null_op_is_mon :> IsMon (A := A) bin_op null_op;
  bin_op_l_act_is_l_sgrp_act :> IsLSgrpAct bin_op l_act;
  null_op_l_act_is_two_l_unl :> IsTwoLUnl null_op l_act;
}.
