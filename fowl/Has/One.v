(** * One or Multiplicative Identity *)

From Maniunfold.Has Require Export
  NullaryOperation.

Class HasOne (A : Type) : Type := one : A.

Typeclasses Transparent HasOne.

Section Context.

Context (A : Type) (x : HasOne A).

(** One is a nullary operation. *)

#[local] Instance has_null_op : HasNullOp A := one.

End Context.

#[export] Hint Resolve has_null_op : typeclass_instances.
