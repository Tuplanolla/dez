From Maniunfold.Has Require Export
  NullaryOperation.

Class HasRUn (A : Type) : Type := r_un : A.

Typeclasses Transparent HasRUn.

Section Context.

Context {A : Type} `{has_r_un : HasRUn A}.

Global Instance A_has_un : HasNullOp A := r_un.

End Context.
