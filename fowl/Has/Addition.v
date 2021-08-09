(** * Addition or Binary Summation *)

From DEZ.Has Require Export
  BinaryOperation.

Class HasAdd (A : Type) : Type := add (x y : A) : A.

Typeclasses Transparent HasAdd.

Module Subclass.

Section Context.

Context (A : Type) (Hk : HasAdd A).

(** Addition is a binary operation. *)

#[local] Instance has_bin_op : HasBinOp A := add.

End Context.

#[export] Hint Resolve has_bin_op : typeclass_instances.

End Subclass.
