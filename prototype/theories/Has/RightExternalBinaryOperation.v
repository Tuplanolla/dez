From Maniunfold.Has Require Export
  BinaryFunction.

Class HasRExBinOp (A B : Type) : Type := r_ex_bin_op : B -> A -> B.

Typeclasses Transparent HasRExBinOp.

Section Context.

Context {A B : Type} `{has_r_ex_bin_op : HasRExBinOp A B}.

Global Instance r_ex_bin_op_has_bin_fn : HasBinFn B A B := r_ex_bin_op.

End Context.
