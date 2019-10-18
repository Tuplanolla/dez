From Maniunfold.Has Require Import
  Homomorphism.

Class HasEndo (A : Type) : Type := endo : A -> A.

Typeclasses Transparent HasEndo.

Section Context.

Context {A : Type} {has_endo : HasEndo A}.

Global Instance : HasHom A A := endo.

End Context.
