From Maniunfold.Has Require Export
  OneSorted.NullaryOperation.

(** Zero, nil, additive identity.
    Commonly found in semirings. *)

Class HasZero (A : Type) : Type := zero : A.

Typeclasses Transparent HasZero.

Section Context.

Context {A : Type} `{A_has_zero : HasZero A}.

Global Instance A_has_null_op : HasNullOp A := zero.

End Context.
