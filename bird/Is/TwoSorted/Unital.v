(* bad *)
From Maniunfold.Has Require Export
  OneSorted.NullaryOperation
  TwoSorted.LeftAction TwoSorted.RightAction.
From Maniunfold.Is Require Export
  TwoSorted.LeftUnital TwoSorted.RightUnital.

Class IsTwoUnl (A B : Type) (A_has_null_op : HasNullOp A)
  (A_B_has_l_act : HasLAct A B) (A_B_has_r_act : HasRAct A B) : Prop := {
  null_op_l_act_is_two_l_unl :> IsTwoLUnl A B null_op l_act;
  null_op_r_act_is_two_r_unl :> IsTwoRUnl A B null_op r_act;
}.
