From Maniunfold.Has Require Export
  OneSorted.UnaryOperation.

(** Reciprocal, multiplicative inverse.
    Commonly found in fields. *)

Class HasRecip (A : Type) : Type := recip : A -> A.

Typeclasses Transparent HasRecip.

Section Context.

Context {A : Type} `{A_has_recip : HasRecip A}.

Global Instance A_has_un_op : HasUnOp A := recip.

End Context.
