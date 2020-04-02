From Maniunfold.Has Require Export
  OneSorted.LeftNullaryOperation OneSorted.RightNullaryOperation
  TwoSorted.LeftAction TwoSorted.RightAction.
From Maniunfold.Is Require Export
  TwoSorted.LeftUnital TwoSorted.RightUnital.

Class IsTwoUnl (A B : Type)
  (A_has_l_null_op : HasLNullOp A) (A_has_r_null_op : HasRNullOp A)
  (A_B_has_l_act : HasLAct A B) (A_B_has_r_act : HasRAct A B) : Prop := {
  l_null_op_l_act_is_two_l_unl :> IsTwoLUnl A B l_null_op l_act;
  r_null_op_r_act_is_two_r_unl :> IsTwoRUnl A B r_null_op r_act;
}.
