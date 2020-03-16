From Maniunfold Require Export
  Init.

Class HasNullOp (A : Type) : Type := null_op : A.

Typeclasses Transparent HasNullOp.
