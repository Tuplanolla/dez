From Maniunfold.Has Require Export
  BinaryFunction.

Class HasLExtBinOp (A B : Type) : Type := l_ext_bin_op : A -> B -> B.

Typeclasses Transparent HasLExtBinOp.

Section Context.

Context {A B : Type} `{has_l_ext_bin_op : HasLExtBinOp A B}.

Global Instance A_B_has_bin_fn : HasBinFn A B B := l_ext_bin_op.

End Context.
