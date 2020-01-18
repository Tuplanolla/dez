From Maniunfold.Has Require Export
  InternalBinaryFunction
  LeftExternalBinaryOperation RightExternalBinaryOperation.

Class HasBinOp (A : Type) : Type := bin_op : A -> A -> A.

Typeclasses Transparent HasBinOp.

Section Context.

Context {A : Type} `{has_bin_op : HasBinOp A}.

Global Instance bin_op_has_in_bin_fn : HasInBinFn A A := bin_op.
Global Instance bin_op_has_l_ex_bin_op : HasLExBinOp A A := bin_op.
Global Instance bin_op_has_r_ex_bin_op : HasRExBinOp A A := bin_op.

End Context.
