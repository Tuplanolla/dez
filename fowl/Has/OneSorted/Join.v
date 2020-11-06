From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.

(** Join, supremum, least upper bound, lattice addition.
    Commonly found in lattices. *)

Class HasJoin (A : Type) : Type := join : A -> A -> A.

Typeclasses Transparent HasJoin.

Section Context.

Context (A : Type) `(HasJoin A).

Global Instance A_has_bin_op : HasBinOp A := join.

End Context.
