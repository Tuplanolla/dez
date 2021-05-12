From Maniunfold.Has Require Export
  OneSortedBinaryOperation OneSortedNullaryOperation.
From Maniunfold.Is Require Export
  OneSortedLeftUnital OneSortedRightUnital TwoSortedUnital.

(** Unital, with an identity. *)

Class IsUnl (A : Type)
  `(HasBinOp A) `(HasNullOp A) : Prop := {
  A_bin_op_null_op_is_l_unl :> IsLUnl bin_op null_op;
  A_bin_op_null_op_is_r_unl :> IsRUnl bin_op null_op;
}.

Section Context.

Context (A : Type) `{IsUnl A}.

Global Instance A_A_bin_op_bin_op_null_op_is_two_unl :
  IsTwoUnl bin_op bin_op null_op.
Proof. split; typeclasses eauto. Defined.

End Context.
