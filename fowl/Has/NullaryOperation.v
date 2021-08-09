(** * Nullary Operation or Identity Element *)

From DEZ Require Export
  Init.

Class HasNullOp (A : Type) : Type := null_op : A.

Typeclasses Transparent HasNullOp.
