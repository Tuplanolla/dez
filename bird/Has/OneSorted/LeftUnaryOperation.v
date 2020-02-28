From Maniunfold.Has Require Export
  LeftFunction UnaryOperation.

Class HasLUnOp (A : Type) : Type := l_un_op : A -> A.

Typeclasses Transparent HasLUnOp.

Section Context.

Context {A : Type} `{has_l_un_op : HasLUnOp A}.

Global Instance A_has_l_fn : HasLFn A A := l_un_op.
Global Instance A_has_un_op : HasUnOp A := l_un_op.

End Context.
