From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation NullaryOperation UnaryOperation
  LeftAction LeftTorsion.
From Maniunfold.Is Require Export
  Group LeftGroupAction LeftUnique.

Class IsLGrpTor {A B : Type}
  (A_has_bin_op : HasBinOp A) (A_has_null_op : HasNullOp A)
  (A_has_un_op : HasUnOp A) (A_B_has_l_act : HasLAct A B)
  (A_B_has_l_tor : HasLTor A B) : Prop := {
  bin_op_null_op_un_op_l_act_is_l_grp_act :> IsLGrpAct bin_op null_op un_op l_act;
  l_act_l_tor_left_uniq :> IsLNullUniq l_act l_tor;
}.
