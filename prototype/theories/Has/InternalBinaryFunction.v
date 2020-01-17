From Maniunfold.Has Require Export
  BinaryFunction.

Class HasInBinFn (A B : Type) : Type := in_bi_fn : A -> A -> B.

Typeclasses Transparent HasInBinFn.

Section Context.

Context {A B : Type} `{has_in_bi_fn : HasInBinFn A B}.

Global Instance in_bi_fn_has_bi_fn : HasBinFn A A B := in_bi_fn.

End Context.
