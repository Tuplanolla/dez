From Maniunfold.Has Require Export
  BinaryFunction.

Class HasBinForm (A B : Type) : Type := bin_form : B -> B -> A.

Typeclasses Transparent HasBinForm.

Section Context.

Context {A B : Type} `{A_B_has_bin_form : HasBinForm A B}.

Global Instance B_B_A_has_bin_fn : HasBinFn B B A := bin_form.

End Context.
