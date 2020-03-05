From Maniunfold.Has Require Export
  Torsion.

Class HasLTor (A B : Type) : Type := l_tor : B -> B -> A.

Typeclasses Transparent HasLTor.

Section Context.

Context {A B : Type} `{has_l_tor : HasLTor A B}.

Global Instance A_B_has_tor : HasTor A B := l_tor.

End Context.
