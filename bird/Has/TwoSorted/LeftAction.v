From Maniunfold.Has Require Export
  ThreeSorted.BinaryFunction.

Class HasLAct (A B : Type) : Type := l_act : A -> B -> B.

Typeclasses Transparent HasLAct.

Section Context.

Context {A B : Type} `{A_has_l_act : HasLAct A B}.

Global Instance A_B_has_bin_fn : HasBinFn A B B := l_act.

End Context.
