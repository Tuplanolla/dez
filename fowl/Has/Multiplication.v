(** * Multiplication or Binary Product *)

From DEZ.Has Require Export
  BinaryOperation.

Class HasMul (A : Type) : Type := mul (x y : A) : A.

Typeclasses Transparent HasMul.

Module Subclass.

Section Context.

Context (A : Type) (Hk : HasMul A).

(** Multiplication is a binary operation. *)

#[local] Instance has_bin_op : HasBinOp A := mul.

End Context.

#[export] Hint Resolve has_bin_op : typeclass_instances.

End Subclass.
