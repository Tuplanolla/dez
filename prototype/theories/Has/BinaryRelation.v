From Maniunfold.Has Require Export
  InternalBinaryFunction.

Class HasBinRel (A : Type) : Type := bin_rel : A -> A -> Prop.

Typeclasses Transparent HasBinRel.

Section Context.

Context {A : Type} `{has_bin_rel : HasBinRel A}.

Global Instance bin_rel_has_bin_fn : HasBinFn A A Prop := bin_rel.

End Context.
