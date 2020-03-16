From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation NullaryOperation UnaryOperation LeftAction.
From Maniunfold.Is Require Export
  Group LeftMonoidAction LeftInvertible.

Class IsLGrpAct {A B : Type}
  (has_bin_op : HasBinOp A) (has_un : HasNullOp A) (has_un_op : HasUnOp A)
  (has_l_act : HasLAct A B) : Prop := {
  bin_op_null_op_un_op_is_grp :> IsGrp (A := A) bin_op null_op un_op;
  bin_op_null_op_l_act_is_l_mon_act :> IsLMonAct bin_op null_op l_act;
  l_act_null_op_un_op_is_l_inv :> IsLInv l_act null_op un_op;
}.
