From Maniunfold.Has Require Export
  OneSorted.NullaryOperation.

Class HasOne (A : Type) : Type := one : A.

Typeclasses Transparent HasOne.

Section Context.

Context {A : Type} `{A_has_one : HasOne A}.

Global Instance A_has_null_op : HasNullOp A := one.

End Context.
