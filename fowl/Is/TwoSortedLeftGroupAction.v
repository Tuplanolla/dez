(* bad *)
From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation UnaryOperation
  Action.
From Maniunfold.Is Require Export
  OneSortedGroup TwoSortedLeftMonoidAction.

Class IsLGrpAct (A B : Type)
  `(HasBinOp A) `(HasNullOp A)
  `(HasUnOp A) `(HasActL A B) : Prop := {
  A_bin_op_null_op_un_op_is_grp :> IsGrp bin_op null_op un_op;
  A_B_bin_op_null_op_act_l_is_l_mon_act :> IsLMonAct bin_op null_op act_l;
}.
