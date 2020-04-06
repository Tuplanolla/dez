(* bad *)
From Maniunfold.Has Require Export
  OneSorted.NullaryOperation.

Class HasLNullOp (A : Type) : Type := l_null_op : A.

Typeclasses Transparent HasLNullOp.

Section Context.

Context {A : Type} `{A_has_l_null_op : HasLNullOp A}.

Global Instance A_has_null_op : HasNullOp A := l_null_op.

End Context.
