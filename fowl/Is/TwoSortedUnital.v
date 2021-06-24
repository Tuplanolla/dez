From Maniunfold.Has Require Export
  Action NullaryOperation.
From Maniunfold.Is Require Export
  TwoSortedLeftUnital TwoSortedRightUnital.

(** Unital.
    See [Is.Unital]. *)

Class IsTwoUnl (A B : Type)
  `(HasActL A B) `(HasActR A B)
  `(HasNullOp A) : Prop := {
  A_B_act_l_null_op_is_two_l_unl :> IsTwoLUnl act_l null_op;
  A_B_act_r_null_op_is_two_r_unl :> IsTwoRUnl act_r null_op;
}.
