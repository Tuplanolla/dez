(** * Reciprocal or Multiplicative Inverse *)

From Maniunfold.Has Require Export
  UnaryOperation.

Class HasRecip (A : Type) : Type := recip (x : A) : A.

Typeclasses Transparent HasRecip.

Section Context.

Context (A : Type) (f : HasRecip A).

(** Reciprocal is a unary operation. *)

#[local] Instance has_un_op : HasUnOp A := recip.

End Context.

#[export] Hint Resolve has_un_op : typeclass_instances.
