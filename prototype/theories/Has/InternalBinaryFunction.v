From Maniunfold.Has Require Export
  BinaryFunction.

Class HasInBinFn (A B : Type) : Type := in_bin_fn : A -> A -> B.

Typeclasses Transparent HasInBinFn.

Section Context.

Context {A B : Type} `{has_in_bin_fn : HasInBinFn A B}.

Global Instance in_bin_fn_has_bin_fn : HasBinFn A A B := in_bin_fn.

End Context.
