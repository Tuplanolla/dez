(** * Unary Operation or Inverse Element *)

From Maniunfold Require Export
  Init.

Class HasUnOp (A : Type) : Type := un_op : A -> A.

Typeclasses Transparent HasUnOp.
