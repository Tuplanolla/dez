From Maniunfold.Has Require Export
  Torsion.

Class HasRTor (A B : Type) : Type := r_tor : A -> A -> B.

Typeclasses Transparent HasRTor.

Section Context.

Context {A B : Type} `{has_r_tor : HasRTor A B}.

Global Instance A_B_has_tor : HasTor A B := r_tor.

End Context.
