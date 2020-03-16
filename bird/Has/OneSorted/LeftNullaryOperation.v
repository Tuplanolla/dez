From Maniunfold.Has Require Export
  NullaryOperation.

Class HasLNullOp (A : Type) : Type := l_null_op : A.

Typeclasses Transparent HasLNullOp.

Section Context.

Context {A : Type} `{has_l_null_op : HasLNullOp A}.

Global Instance A_has_un : HasNullOp A := l_null_op.

End Context.
