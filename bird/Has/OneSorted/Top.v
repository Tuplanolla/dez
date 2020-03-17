From Maniunfold.Has Require Export
  NullaryOperation.

Class HasTop (A : Type) : Type := top : A.

Typeclasses Transparent HasTop.

Section Context.

Context {A : Type} `{has_top : HasTop A}.

Global Instance A_has_null_op : HasNullOp A := top.

End Context.
