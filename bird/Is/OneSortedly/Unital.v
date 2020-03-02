From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit.
From Maniunfold.Is Require Export
  OneSortedly.LeftUnital OneSortedly.RightUnital TwoSortedly.Unital.

Class IsUnl {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop := {
  bin_op_un_is_l_unl :> IsLUnl bin_op un;
  bin_op_un_is_r_unl :> IsRUnl bin_op un;
}.

Section Context.

Context {A : Type} `{is_unl : IsUnl A}.

Global Instance un_bin_op_is_unl_2 : IsUnl2 un un bin_op bin_op.
Proof.
  constructor.
  - destruct is_unl; typeclasses eauto.
  - destruct is_unl; typeclasses eauto. Qed.

End Context.
