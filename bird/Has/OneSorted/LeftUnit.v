From Maniunfold.Has Require Export
  NullaryOperation.

Class HasLUn (A : Type) : Type := l_un : A.

Typeclasses Transparent HasLUn.

Section Context.

Context {A : Type} `{has_l_un : HasLUn A}.

Global Instance A_has_un : HasNullOp A := l_un.

End Context.
