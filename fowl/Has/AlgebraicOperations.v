(** * Operations *)

From DEZ Require Export
  Init.

(** ** Nullary Operation *)

Class HasNullOp (A : Type) : Type := null_op : A.

#[export] Typeclasses Transparent HasNullOp.

(** * Unary Operation *)

Class HasUnOp (A : Type) : Type := un_op (x : A) : A.

#[export] Typeclasses Transparent HasUnOp.

(** * Binary Operation *)

Class HasBinOp (A : Type) : Type := bin_op (x y : A) : A.

#[export] Typeclasses Transparent HasBinOp.
