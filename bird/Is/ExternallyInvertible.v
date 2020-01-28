From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit UnaryOperation.
From Maniunfold.Is Require Export
  LeftExternallyInvertible RightExternallyInvertible InternallyInvertible.

Class IsExtInv {A : Type} {has_bin_rel : HasBinRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A)
  (has_un_op : HasUnOp A) : Prop := {
  bin_op_un_un_op_is_l_ext_inv :> IsLExtInv bin_op un un_op;
  bin_op_un_un_op_is_r_ext_inv :> IsRExtInv bin_op un un_op;
}.

Section Context.

Context {A : Type} `{is_ext_inv : IsExtInv A}.

Global Instance bin_op_un_un_op_is_int_inv : IsIntInv bin_op un un_op.
Proof.
  constructor.
  - destruct is_ext_inv; typeclasses eauto.
  - destruct is_ext_inv; typeclasses eauto. Qed.

End Context.
