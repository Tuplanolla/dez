From Maniunfold.Has Require Export
  OneSortedNullaryOperation.

(** Top, maximum, greatest element, lattice one.
    Commonly found in bounded lattices. *)

Class HasTop (A : Type) : Type := top : A.

Typeclasses Transparent HasTop.

Section Context.

Context (A : Type) `(HasTop A).

Global Instance A_has_null_op : HasNullOp A := top.

End Context.
