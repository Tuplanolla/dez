From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.

(** Multiplication, binary product, times.
    Commonly found in semirings. *)

Class HasMul (A : Type) : Type := mul : A -> A -> A.

Typeclasses Transparent HasMul.

Section Context.

Context {A : Type} `{A_has_mul : HasMul A}.

Global Instance A_has_bin_op : HasBinOp A := mul.

End Context.
