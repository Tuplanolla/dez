From Maniunfold.Has Require Export
  Unit.

Class HasZero (A : Type) : Type := zero : A.

Typeclasses Transparent HasZero.

Section Context.

Context {A : Type} `{has_zero : HasZero A}.

Global Instance A_has_un : HasUn A := zero.

End Context.
