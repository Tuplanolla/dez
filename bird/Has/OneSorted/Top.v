From Maniunfold.Has Require Export
  Unit.

Class HasTop (A : Type) : Type := top : A.

Typeclasses Transparent HasTop.

Section Context.

Context {A : Type} `{has_top : HasTop A}.

Global Instance A_has_un : HasUn A := top.

End Context.
