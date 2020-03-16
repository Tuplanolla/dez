From Maniunfold.Has Require Export
  NullaryOperation.

Class HasOne (A : Type) : Type := one : A.

Typeclasses Transparent HasOne.

Section Context.

Context {A : Type} `{has_one : HasOne A}.

Global Instance A_has_un : HasNullOp A := one.

End Context.
