From Maniunfold.Has Require Export
  BinaryFunction.

Class HasTor (A B : Type) : Type := tor : A -> A -> B.

Typeclasses Transparent HasTor.

Section Context.

Context {A B : Type} `{has_tor : HasTor A B}.

Global Instance A_B_has_bin_fn : HasBinFn A A B := tor.

End Context.
