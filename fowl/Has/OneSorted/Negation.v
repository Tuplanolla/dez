From Maniunfold.Has Require Export
  OneSorted.UnaryOperation.

(** Negation, opposite, additive inverse.
    Commonly found in rings. *)

Class HasNeg (A : Type) : Type := neg : A -> A.

Typeclasses Transparent HasNeg.

Section Context.

Context (A : Type) `(HasNeg A).

Global Instance A_has_un_op : HasUnOp A := neg.

End Context.
