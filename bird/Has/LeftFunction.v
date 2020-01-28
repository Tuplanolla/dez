From Maniunfold.Has Require Export
  Function.

Class HasLFn (A B : Type) : Type := l_fn : A -> B.

Typeclasses Transparent HasLFn.

Section Context.

Context {A B : Type} `{has_l_fn : HasLFn A B}.

Global Instance A_B_has_fn : HasFn A B := l_fn.

End Context.
