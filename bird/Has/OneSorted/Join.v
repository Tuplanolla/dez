From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.

Class HasJoin (A : Type) : Type := join : A -> A -> A.

Typeclasses Transparent HasJoin.

Section Context.

Context {A : Type} `{A_has_join : HasJoin A}.

Global Instance A_has_bin_op : HasBinOp A := join.

End Context.
