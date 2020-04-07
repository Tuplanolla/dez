(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation.
From Maniunfold.Is Require Export
  OneSorted.LeftUnital OneSorted.RightUnital TwoSorted.Unital.

Class IsUnl {A : Type}
  (A_has_bin_op : HasBinOp A) (A_has_null_op : HasNullOp A) : Prop := {
  bin_op_null_op_is_l_unl :> IsLUnl bin_op null_op;
  bin_op_null_op_is_r_unl :> IsRUnl bin_op null_op;
}.

Section Context.

Context {A : Type} `{is_unl : IsUnl A}.

Global Instance A_A_null_op_bin_op_bin_op_is_two_unl :
  IsTwoUnl A A null_op bin_op bin_op.
Proof.
  split.
  - destruct is_unl; typeclasses eauto.
  - destruct is_unl; typeclasses eauto. Qed.

End Context.
