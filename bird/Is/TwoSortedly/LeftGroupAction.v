From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit UnaryOperation LeftAction.
From Maniunfold.Is Require Export
  Group LeftMonoidAction LeftInvertible.

Class IsLGrpAct {A B : Type}
  {A_has_eq_rel : HasEqRel A} {B_has_eq_rel : HasEqRel B}
  (has_bin_op : HasBinOp A) (has_un : HasUn A) (has_un_op : HasUnOp A)
  (has_l_act : HasLAct A B) : Prop := {
  bin_op_un_un_op_is_grp :> IsGrp bin_op un un_op;
  bin_op_un_l_act_is_l_mon_act :> IsLMonAct bin_op un l_act;
  l_act_un_un_op_is_l_inv :> IsLInv l_act un un_op;
}.
