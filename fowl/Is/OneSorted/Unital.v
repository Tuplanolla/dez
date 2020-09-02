From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation.
From Maniunfold.Is Require Export
  OneSorted.LeftUnital OneSorted.RightUnital TwoSorted.Unital.

(** Unital, with an identity. *)

Class IsUnl (A : Type)
  (A_has_bin_op : HasBinOp A) (A_has_null_op : HasNullOp A) : Prop := {
  A_bin_op_null_op_is_l_unl :> IsLUnl A bin_op null_op;
  A_bin_op_null_op_is_r_unl :> IsRUnl A bin_op null_op;
}.

Section Context.

Context {A : Type} `{is_unl : IsUnl A}.

Global Instance A_A_bin_op_bin_op_null_op_is_two_unl :
  IsTwoUnl A A bin_op bin_op null_op.
Proof. split; typeclasses eauto. Defined.

End Context.
