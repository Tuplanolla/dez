From Maniunfold.Has Require Export
  NullaryOperation.

Class HasRNullOp (A : Type) : Type := r_null_op : A.

Typeclasses Transparent HasRNullOp.

Section Context.

Context {A : Type} `{has_r_null_op : HasRNullOp A}.

Global Instance A_has_un : HasNullOp A := r_null_op.

End Context.
