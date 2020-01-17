From Maniunfold.Has Require Export
  InternalBinaryFunction
  LeftExternalBinaryOperation RightExternalBinaryOperation.

Class HasBiOp (A : Type) : Type := bi_op : A -> A -> A.

Typeclasses Transparent HasBiOp.

Section Context.

Context {A : Type} `{has_bi_op : HasBiOp A}.

Global Instance bi_op_has_in_bi_fn : HasInBiFn A A := bi_op.

Global Instance bi_op_has_l_ex_bi_op : HasLExBiOp A A := bi_op.

Global Instance bi_op_has_r_ex_bi_op : HasRExBiOp A A := bi_op.

End Context.
