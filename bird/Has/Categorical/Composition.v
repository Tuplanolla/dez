From Maniunfold.Has Require Export
  Categorical.Morphism.
From Maniunfold.ShouldHave Require Import
  Categorical.TypeNotations.

Class HasComp {A : Type} (has_hom : HasHom A) : Type :=
  comp : forall x y z : A, (x --> y) -> (y --> z) -> (x --> z).

Typeclasses Transparent HasComp.
