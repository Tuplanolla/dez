From Maniunfold.Has.OneSorted Require Export
  BinaryOperation Unit.
From Maniunfold.Is Require Export
  OneSortedly.LeftUnital OneSortedly.RightUnital TwoSortedly.Unital.

Class IsUnl {A : Type} (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop := {
  bin_op_un_is_l_unl :> IsLUnl bin_op un;
  bin_op_un_is_r_unl :> IsRUnl bin_op un;
}.

Section Context.

Context {A : Type} `{is_unl : IsUnl A}.

Global Instance un_un_bin_op_bin_op_is_two_unl : IsTwoUnl un un bin_op bin_op.
Proof.
  constructor.
  - destruct is_unl; typeclasses eauto.
  - destruct is_unl; typeclasses eauto. Qed.

End Context.
