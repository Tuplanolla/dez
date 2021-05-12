From Maniunfold.Has Require Export
  OneSortedBinaryOperation.

(** Addition, summation, plus.
    Commonly found in semirings. *)

Class HasAdd (A : Type) : Type := add : A -> A -> A.

Typeclasses Transparent HasAdd.

Section Context.

Context (A : Type) `(HasAdd A).

Global Instance A_has_bin_op : HasBinOp A := add.

End Context.
