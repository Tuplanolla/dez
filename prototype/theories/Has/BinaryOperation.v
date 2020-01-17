From Maniunfold.Has Require Export
  InternalBinaryFunction
  LeftExternalBinaryOperation RightExternalBinaryOperation.

Class HasBinOp (A : Type) : Type := bi_op : A -> A -> A.

Typeclasses Transparent HasBinOp.

Section Context.

Context {A : Type} `{has_bi_op : HasBinOp A}.

Global Instance bi_op_has_in_bi_fn : HasInBinFn A A := bi_op.

Global Instance bi_op_has_l_ex_bi_op : HasLExBinOp A A := bi_op.

Global Instance bi_op_has_r_ex_bi_op : HasRExBinOp A A := bi_op.

End Context.
