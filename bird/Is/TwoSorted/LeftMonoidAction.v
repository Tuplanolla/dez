(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation TwoSorted.LeftAction.
From Maniunfold.Is Require Export
  OneSorted.Monoid TwoSorted.LeftSemigroupAction TwoSorted.LeftUnital.

Class IsLMonAct (A B : Type)
  (A_has_bin_op : HasBinOp A) (A_has_null_op : HasNullOp A)
  (A_B_has_l_act : HasLAct A B) : Prop := {
  A_bin_op_null_op_is_mon :> IsMon (A := A) bin_op null_op;
  A_B_bin_op_l_act_is_l_sgrp_act :> IsLSgrpAct A B bin_op l_act;
  A_B_null_op_l_act_is_two_l_unl :> IsTwoLUnl A B null_op l_act;
}.
