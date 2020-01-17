From Maniunfold.Has Require Export
  BinaryFunction.

Class HasInBiFn (A B : Type) : Type := in_bi_fn : A -> A -> B.

Typeclasses Transparent HasInBiFn.

Section Context.

Context {A B : Type} `{has_in_bi_fn : HasInBiFn A B}.

Global Instance in_bi_fn_has_bi_fn : HasBiFn A A B := in_bi_fn.

End Context.
