From Maniunfold.Has Require Export
  TwoSorted.LeftAction TwoSorted.RightAction OneSorted.NullaryOperation.
From Maniunfold.Is Require Export
  TwoSorted.LeftUnital TwoSorted.RightUnital.

(** Unital.
    See [Is.OneSorted.Unital]. *)

Class IsTwoUnl (A B : Type)
  `(HasLAct A B) `(HasRAct A B)
  `(HasNullOp A) : Prop := {
  A_B_l_act_null_op_is_two_l_unl :> IsTwoLUnl A B l_act null_op;
  A_B_r_act_null_op_is_two_r_unl :> IsTwoRUnl A B r_act null_op;
}.
