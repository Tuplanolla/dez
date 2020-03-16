From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation NullaryOperation.
From Maniunfold.Is Require Export
  LeftUnital RightUnital.

Class IsTwoUnl {A B : Type}
  (has_l_null_op : HasLNullOp A) (has_r_null_op : HasRNullOp A)
  (has_l_act : HasLAct A B) (has_r_act : HasRAct A B) : Prop := {
  l_null_op_l_act_is_two_l_unl_ :> IsTwoLUnl l_null_op l_act;
  r_null_op_r_act_is_two_r_unl_ :> IsTwoRUnl r_null_op r_act;
}.
