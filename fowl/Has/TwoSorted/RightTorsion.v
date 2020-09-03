From Maniunfold.Has Require Export
  Torsion.

(** Torsion, the unique element associated with an action; left chirality.
    Commonly found in torsors. *)

Class HasRTor (A B : Type) : Type := r_tor : B -> B -> A.

Typeclasses Transparent HasRTor.

Section Context.

Context {A B : Type} `{A_B_has_r_tor : HasRTor A B}.

Global Instance A_B_has_tor : HasTor A B := r_tor.

End Context.