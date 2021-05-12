From Maniunfold.Has Require Export
  TwoSortedLeftAction TwoSortedRightAction OneSortedNullaryOperation.
From Maniunfold.Is Require Export
  TwoSortedLeftUnital TwoSortedRightUnital.

(** Unital.
    See [Is.OneSortedUnital]. *)

Class IsTwoUnl (A B : Type)
  `(HasLAct A B) `(HasRAct A B)
  `(HasNullOp A) : Prop := {
  A_B_l_act_null_op_is_two_l_unl :> IsTwoLUnl l_act null_op;
  A_B_r_act_null_op_is_two_r_unl :> IsTwoRUnl r_act null_op;
}.
