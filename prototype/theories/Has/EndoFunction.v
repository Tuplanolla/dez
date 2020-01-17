From Maniunfold.Has Require Export
  Function.

Class HasEndoFn (A : Type) : Type := endo_fn : A -> A.

Typeclasses Transparent HasEndoFn.

Section Context.

Context {A : Type} `{has_endo_fn : HasEndoFn A}.

Global Instance endo_fn_has_fn : HasFn A A := endo_fn.

End Context.
