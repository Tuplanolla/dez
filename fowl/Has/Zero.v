(** * Zero or Additive Identity *)

From Maniunfold.Has Require Export
  NullaryOperation.

Class HasZero (A : Type) : Type := zero : A.

Typeclasses Transparent HasZero.

Module Subclass.

Section Context.

Context (A : Type) (Hx : HasZero A).

(** Zero is a nullary operation. *)

#[local] Instance has_null_op : HasNullOp A := zero.

End Context.

#[export] Hint Resolve has_null_op : typeclass_instances.

End Subclass.
