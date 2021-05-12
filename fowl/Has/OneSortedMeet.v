From Maniunfold.Has Require Export
  OneSortedBinaryOperation.

(** Meet, infimum, greatest lower bound, lattice multiplication.
    Commonly found in lattices. *)

Class HasMeet (A : Type) : Type := meet : A -> A -> A.

Typeclasses Transparent HasMeet.

Section Context.

Context (A : Type) `(HasMeet A).

Global Instance A_has_bin_op : HasBinOp A := meet.

End Context.
