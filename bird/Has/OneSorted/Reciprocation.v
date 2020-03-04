From Maniunfold.Has Require Export
  UnaryOperation.

Class HasRecip (A : Type) : Type := recip : A -> A.

Typeclasses Transparent HasRecip.

Section Context.

Context {A : Type} `{has_recip : HasRecip A}.

Global Instance A_has_un_op : HasUnOp A := recip.

End Context.