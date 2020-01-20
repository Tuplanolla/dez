From Maniunfold.Has Require Export
  BinaryFunction.

Class HasRExtBinOp (A B : Type) : Type := r_ext_bin_op : B -> A -> B.

Typeclasses Transparent HasRExtBinOp.

Section Context.

Context {A B : Type} `{has_r_ext_bin_op : HasRExtBinOp A B}.

Global Instance r_ext_bin_op_has_bin_fn : HasBinFn B A B := r_ext_bin_op.

End Context.
