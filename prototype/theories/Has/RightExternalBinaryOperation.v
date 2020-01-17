From Maniunfold.Has Require Export
  BinaryFunction.

Class HasRExBinOp (A B : Type) : Type := r_ex_bi_op : B -> A -> B.

Typeclasses Transparent HasRExBinOp.

Section Context.

Context {A B : Type} `{has_r_ex_bi_op : HasRExBinOp A B}.

Global Instance r_ex_bi_op_has_bi_fn : HasBinFn B A B := r_ex_bi_op.

End Context.
