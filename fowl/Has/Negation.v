(** * Negation or Additive Inverse *)

From DEZ.Has Require Export
  UnaryOperation.

Class HasNeg (A : Type) : Type := neg (x : A) : A.

Typeclasses Transparent HasNeg.

Module Subclass.

Section Context.

Context (A : Type) (Hf : HasNeg A).

(** Negation is a unary operation. *)

#[local] Instance has_un_op : HasUnOp A := neg.

End Context.

#[export] Hint Resolve has_un_op : typeclass_instances.

End Subclass.
