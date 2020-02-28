From Maniunfold.Has Require Export
  InternalBinaryFunction
  LeftAction RightAction.

Class HasBinOp (A : Type) : Type := bin_op : A -> A -> A.

Typeclasses Transparent HasBinOp.

Section Context.

Context {A : Type} `{has_bin_op : HasBinOp A}.

Global Instance A_has_int_bin_fn : HasIntBinFn A A := bin_op.
Global Instance A_has_l_act : HasLAct A A := bin_op.
Global Instance A_has_r_act : HasRAct A A := bin_op.

End Context.
