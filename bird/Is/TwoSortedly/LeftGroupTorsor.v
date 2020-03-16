From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation NullaryOperation UnaryOperation
  LeftAction LeftTorsion.
From Maniunfold.Is Require Export
  Group LeftGroupAction LeftUnique.

Class IsLGrpTor {A B : Type}
  (has_bin_op : HasBinOp A) (has_null_op : HasNullOp A) (has_un_op : HasUnOp A)
  (has_l_act : HasLAct A B) (has_l_tor : HasLTor A B) : Prop := {
  bin_op_null_op_un_op_l_act_is_l_grp_act :> IsLGrpAct bin_op null_op un_op l_act;
  l_act_l_tor_left_uniq :> IsLNullUniq l_act l_tor;
}.
