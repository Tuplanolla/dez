From Maniunfold.Has Require Export
  BinaryFunction.

Class HasRExBiOp (A B : Type) : Type := r_ex_bi_op : B -> A -> B.

Typeclasses Transparent HasRExBiOp.

Section Context.

Context {A B : Type} `{has_r_ex_bi_op : HasRExBiOp A B}.

Global Instance r_ex_bi_op_has_bi_fn : HasBiFn B A B := r_ex_bi_op.

End Context.
