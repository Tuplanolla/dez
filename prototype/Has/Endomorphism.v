From Maniunfold.Has Require Import
  Homomorphism.

Class HasEndo (A : Type) : Type := endo : A -> A.

Typeclasses Transparent HasEndo.

Instance endo_has_hom {A : Type} {has_endo : HasEndo A} : HasHom A A := endo.
