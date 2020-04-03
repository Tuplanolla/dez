From Maniunfold.Has Require Export
  ThreeSorted.BinaryFunction.

Class HasTor (A B : Type) : Type := tor : B -> B -> A.

Typeclasses Transparent HasTor.

Section Context.

Context {A B : Type} `{A_B_has_tor : HasTor A B}.

Global Instance B_B_A_has_bin_fn : HasBinFn B B A := tor.

End Context.
