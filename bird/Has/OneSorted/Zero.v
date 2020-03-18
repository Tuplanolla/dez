From Maniunfold.Has Require Export
  OneSorted.NullaryOperation.

Class HasZero (A : Type) : Type := zero : A.

Typeclasses Transparent HasZero.

Section Context.

Context {A : Type} `{has_zero : HasZero A}.

Global Instance A_has_un : HasNullOp A := zero.

End Context.
