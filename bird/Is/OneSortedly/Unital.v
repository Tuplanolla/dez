From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation.
From Maniunfold.Is Require Export
  OneSortedly.LeftUnital OneSortedly.RightUnital TwoSortedly.Unital.

Class IsUnl {A : Type}
  (A_has_bin_op : HasBinOp A) (A_has_null_op : HasNullOp A) : Prop := {
  bin_op_null_op_is_l_unl :> IsLUnl bin_op null_op;
  bin_op_null_op_is_r_unl :> IsRUnl bin_op null_op;
}.

Section Context.

Context {A : Type} `{is_unl : IsUnl A}.

Global Instance null_op_un_bin_op_bin_op_is_two_unl : IsTwoUnl null_op null_op bin_op bin_op.
Proof.
  constructor.
  - destruct is_unl; typeclasses eauto.
  - destruct is_unl; typeclasses eauto. Qed.

End Context.
