From Maniunfold.Has Require Export
  Torsion.

(** Torsion, principal homogeneous space action; left chirality.
    Commonly found in torsors. *)

Class HasLTor (A B : Type) : Type := l_tor : B -> B -> A.

Typeclasses Transparent HasLTor.

Section Context.

Context (A B : Type) `(HasLTor A B).

Global Instance A_B_has_tor : HasTor A B := l_tor.

End Context.
