From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit.
From Maniunfold.Is Require Export
  LeftUnital RightUnital ExternallyUnital.

Class IsUnl {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop := {
  bin_op_un_is_l_unl :> IsLUnl bin_op un;
  bin_op_un_is_r_unl :> IsRUnl bin_op un;
}.

Section Context.

Context {A : Type} `{is_unl : IsUnl A}.

Global Instance bin_op_un_is_ext_unl : IsExtUnl bin_op un un.
Proof.
  constructor.
  - destruct is_unl; typeclasses eauto.
  - destruct is_unl; typeclasses eauto. Qed.

End Context.
