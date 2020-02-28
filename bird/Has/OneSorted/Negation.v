From Maniunfold.Has Require Export
  UnaryOperation.

Class HasNeg (A : Type) : Type := neg : A -> A.

Typeclasses Transparent HasNeg.

Section Context.

Context {A : Type} `{has_neg : HasNeg A}.

Global Instance A_has_un_op : HasUnOp A := neg.

End Context.
