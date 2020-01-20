From Maniunfold.Has Require Export
  InternalBinaryFunction.

Class HasBinRel (A : Type) : Type := bin_rel : A -> A -> Prop.

Typeclasses Transparent HasBinRel.

Section Context.

Context {A : Type} `{has_bin_rel : HasBinRel A}.

Global Instance bin_rel_has_int_bin_fn : HasIntBinFn A Prop := bin_rel.

End Context.
