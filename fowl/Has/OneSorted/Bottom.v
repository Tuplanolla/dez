From Maniunfold.Has Require Export
  OneSorted.NullaryOperation.

(** Bottom, minimum, least element, lattice zero.
    Commonly found in bounded lattices. *)

Class HasBot (A : Type) : Type := bot : A.

Typeclasses Transparent HasBot.

Section Context.

Context (A : Type) `(HasBot A).

Global Instance A_has_null_op : HasNullOp A := bot.

End Context.
