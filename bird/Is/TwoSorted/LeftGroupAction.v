From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation UnaryOperation LeftAction.
From Maniunfold.Is Require Export
  Group LeftMonoidAction LeftInvertible.

Class IsLGrpAct (A B : Type)
  (A_has_bin_op : HasBinOp A) (A_has_null_op : HasNullOp A)
  (A_has_un_op : HasUnOp A) (A_B_has_l_act : HasLAct A B) : Prop := {
  bin_op_null_op_un_op_is_grp :> IsGrp (A := A) bin_op null_op un_op;
  bin_op_null_op_l_act_is_l_mon_act :> IsLMonAct A B bin_op null_op l_act;
  l_act_null_op_un_op_is_l_inv :> IsLInv l_act null_op un_op;
}.
