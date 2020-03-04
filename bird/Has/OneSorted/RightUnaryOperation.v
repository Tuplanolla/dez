From Maniunfold.Has Require Export
  RightFunction UnaryOperation.

Class HasRUnOp (A : Type) : Type := r_un_op : A -> A.

Typeclasses Transparent HasRUnOp.

Section Context.

Context {A : Type} `{has_r_un_op : HasRUnOp A}.

Global Instance A_has_r_fn : HasRFn A A := r_un_op.
Global Instance A_has_un_op : HasUnOp A := r_un_op.

End Context.