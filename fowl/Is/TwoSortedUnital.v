From DEZ.Has Require Export
  ArithmeticOperations ArithmeticActions.
From DEZ.Is Require Export
  TwoSortedLeftUnital TwoSortedRightUnital.

(** Unital.
    See [Is.Unital]. *)

Class IsTwoUnl (A B : Type)
  `(HasActL A B) `(HasActR A B)
  `(HasNullOp A) : Prop := {
  A_B_act_l_null_op_is_two_unl_l :> IsTwoUnlL act_l null_op;
  A_B_act_r_null_op_is_two_unl_r :> IsTwoUnlR act_r null_op;
}.
