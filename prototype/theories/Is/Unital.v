From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit.
From Maniunfold.Is Require Export
  LeftUnital RightUnital ExternallyUnital.

Class IsUn {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop := {
  bin_op_un_is_l_un :> IsLUn bin_op un;
  bin_op_un_is_r_un :> IsRUn bin_op un;
}.

Section Context.

Context {A : Type} `{is_un : IsUn A}.

Global Instance bin_op_un_is_ext_un : IsExtUn bin_op un.
Proof.
  constructor.
  - intros x. apply l_un.
  - intros x. apply r_un. Qed.

End Context.
