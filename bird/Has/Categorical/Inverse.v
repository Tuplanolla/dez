From Maniunfold.Has Require Export
  Categorical.Morphism.
From Maniunfold.ShouldHave Require Import
  Categorical.TypeNotations.

Class HasInv {A : Type} (has_hom : HasHom A) : Type :=
  inv : forall x y : A, (x --> y) -> (y --> x).

Typeclasses Transparent HasInv.
