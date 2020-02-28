From Maniunfold.Has Require Export
  Function.

Class HasUnOp (A : Type) : Type := un_op : A -> A.

Typeclasses Transparent HasUnOp.

Section Context.

Context {A : Type} `{has_un_op : HasUnOp A}.

Global Instance A_has_fn : HasFn A A := un_op.

End Context.
