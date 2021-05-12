From Maniunfold.Has Require Export
  OneSortedBinaryOperation.

(** Multiplication, binary product, times.
    Commonly found in semirings. *)

Class HasMul (A : Type) : Type := mul : A -> A -> A.

Typeclasses Transparent HasMul.

Section Context.

Context (A : Type) `(HasMul A).

Global Instance A_has_bin_op : HasBinOp A := mul.

End Context.
