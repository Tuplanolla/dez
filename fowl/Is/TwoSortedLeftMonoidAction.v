(* bad *)
From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation Action.
From Maniunfold.Is Require Export
  OneSortedMonoid TwoSortedLeftSemigroupAction TwoSortedLeftUnital.

Class IsLMonAct (A B : Type)
  `(HasBinOp A) `(HasNullOp A)
  `(HasActL A B) : Prop := {
  A_bin_op_null_op_is_mon :> IsMon bin_op null_op;
  A_B_bin_op_act_l_is_l_semigrp_act :> IsLSemigrpAct bin_op act_l;
  A_B_null_op_act_l_is_two_l_unl :> IsTwoLUnl act_l null_op;
}.
