From Maniunfold.Has Require Export
  InternalBinaryFunction ExternalBinaryOperation.

Class HasBiOp (A : Type) : Type := bi_op : A -> A -> A.

Typeclasses Transparent HasBiOp.

Section Context.

Context {A : Type} `{has_bi_op : HasBiOp A}.

Global Instance bi_op_has_in_bi_fn : HasInBiFn A A := bi_op.

Global Instance bi_op_has_ex_bi_op : HasExBiOp A A := bi_op.

End Context.
