(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation TwoSorted.LeftAction.
From Maniunfold.Is Require Export
  OneSorted.Monoid TwoSorted.LeftSemigroupAction TwoSorted.LeftUnital.

Class IsLMonAct (A B : Type)
  `(HasBinOp A) `(HasNullOp A)
  `(HasLAct A B) : Prop := {
  A_bin_op_null_op_is_mon :> IsMon A bin_op null_op;
  A_B_bin_op_l_act_is_l_sgrp_act :> IsLSgrpAct A B bin_op l_act;
  A_B_null_op_l_act_is_two_l_unl :> IsTwoLUnl A B l_act null_op;
}.
