From Maniunfold.Has Require Export
  Unit.

Class HasOne (A : Type) : Type := one : A.

Typeclasses Transparent HasOne.

Section Context.

Context {A : Type} `{has_one : HasOne A}.

Global Instance A_has_un : HasUn A := one.

End Context.
