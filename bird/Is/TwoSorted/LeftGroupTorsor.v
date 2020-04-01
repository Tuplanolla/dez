From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation OneSorted.UnaryOperation
  TwoSorted.LeftAction TwoSorted.LeftTorsion.
From Maniunfold.Is Require Export
  OneSorted.Group TwoSorted.LeftGroupAction TwoSorted.LeftUnique.

Class IsLGrpTor (A B : Type)
  (A_has_bin_op : HasBinOp A) (A_has_null_op : HasNullOp A)
  (A_has_un_op : HasUnOp A) (A_B_has_l_act : HasLAct A B)
  (A_B_has_l_tor : HasLTor A B) : Prop := {
  bin_op_null_op_un_op_l_act_is_l_grp_act :>
    IsLGrpAct A B bin_op null_op un_op l_act;
  l_act_l_tor_l_uniq :> IsLUniq A B l_act l_tor;
}.
