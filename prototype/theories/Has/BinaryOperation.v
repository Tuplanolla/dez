From Maniunfold.Has Require Export
  InternalBinaryFunction
  LeftExternalBinaryOperation RightExternalBinaryOperation.

Class HasBinOp (A : Type) : Type := bin_op : A -> A -> A.

Typeclasses Transparent HasBinOp.

Section Context.

Context {A : Type} `{has_bin_op : HasBinOp A}.

Global Instance bin_op_has_int_bin_fn : HasIntBinFn A A := bin_op.
Global Instance bin_op_has_l_ext_bin_op : HasLExtBinOp A A := bin_op.
Global Instance bin_op_has_r_ext_bin_op : HasRExtBinOp A A := bin_op.

End Context.
