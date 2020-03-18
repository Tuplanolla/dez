From Maniunfold.Has Require Export
  BinaryFunction.

Class HasRAct (A B : Type) : Type := r_act : B -> A -> B.

Typeclasses Transparent HasRAct.

Section Context.

Context {A B : Type} `{A_has_r_act : HasRAct A B}.

Global Instance A_B_has_bin_fn : HasBinFn B A B := r_act.

End Context.
