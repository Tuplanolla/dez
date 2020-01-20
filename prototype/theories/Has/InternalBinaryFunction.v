From Maniunfold.Has Require Export
  BinaryFunction.

Class HasIntBinFn (A B : Type) : Type := int_bin_fn : A -> A -> B.

Typeclasses Transparent HasIntBinFn.

Section Context.

Context {A B : Type} `{has_int_bin_fn : HasIntBinFn A B}.

Global Instance int_bin_fn_has_bin_fn : HasBinFn A A B := int_bin_fn.

End Context.
