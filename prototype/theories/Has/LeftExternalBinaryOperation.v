From Maniunfold.Has Require Export
  BinaryFunction.

Class HasLExBinOp (A B : Type) : Type := l_ex_bi_op : A -> B -> B.

Typeclasses Transparent HasLExBinOp.

Section Context.

Context {A B : Type} `{has_l_ex_bi_op : HasLExBinOp A B}.

Global Instance l_ex_bi_op_has_bi_fn : HasBinFn A B B := l_ex_bi_op.

End Context.
