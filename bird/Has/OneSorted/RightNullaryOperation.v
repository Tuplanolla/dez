From Maniunfold.Has Require Export
  OneSorted.NullaryOperation.

Class HasRNullOp (A : Type) : Type := r_null_op : A.

Typeclasses Transparent HasRNullOp.

Section Context.

Context {A : Type} `{A_has_r_null_op : HasRNullOp A}.

Global Instance A_has_null_op : HasNullOp A := r_null_op.

End Context.
