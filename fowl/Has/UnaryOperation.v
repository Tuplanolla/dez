(** * Unary Operation or Inverse Element *)

From DEZ Require Export
  Init.

Class HasUnOp (A : Type) : Type := un_op (x : A) : A.

Typeclasses Transparent HasUnOp.
