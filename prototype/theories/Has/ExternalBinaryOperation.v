From Maniunfold.Has Require Export
  BinaryFunction.

Class HasExBiOp (A B : Type) : Type := ex_bi_op : A -> B -> B.

Typeclasses Transparent HasExBiOp.

Section Context.

Context {A B : Type} `{has_ex_bi_op : HasExBiOp A B}.

Global Instance ex_bi_op_has_bi_fn : HasBiFn A B B := ex_bi_op.

End Context.
