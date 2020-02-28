From Maniunfold.Has Require Export
  Function.

Class HasRFn (A B : Type) : Type := r_fn : A -> B.

Typeclasses Transparent HasRFn.

Section Context.

Context {A B : Type} `{has_r_fn : HasRFn A B}.

Global Instance A_B_has_fn : HasFn A B := r_fn.

End Context.
