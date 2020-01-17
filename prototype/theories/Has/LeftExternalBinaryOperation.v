From Maniunfold.Has Require Export
  BinaryFunction.

Class HasLExBiOp (A B : Type) : Type := l_ex_bi_op : A -> B -> B.

Typeclasses Transparent HasLExBiOp.

Section Context.

Context {A B : Type} `{has_l_ex_bi_op : HasLExBiOp A B}.

Global Instance l_ex_bi_op_has_bi_fn : HasBiFn A B B := l_ex_bi_op.

End Context.
