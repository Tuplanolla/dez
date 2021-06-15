From Maniunfold.Has Require Export
  NullaryOperation.

(** One, unity, multiplicative identity.
    Commonly found in semirings. *)

Class HasOne (A : Type) : Type := one : A.

Typeclasses Transparent HasOne.

Section Context.

Context (A : Type) `(HasOne A).

Global Instance A_has_null_op : HasNullOp A := one.

End Context.
