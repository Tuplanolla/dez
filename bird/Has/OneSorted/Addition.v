From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.

Class HasAdd (A : Type) : Type := add : A -> A -> A.

Typeclasses Transparent HasAdd.

Section Context.

Context {A : Type} `{A_has_add : HasAdd A}.

Global Instance A_has_bin_op : HasBinOp A := add.

End Context.
