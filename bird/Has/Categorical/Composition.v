From Maniunfold.Has Require Export
  Morphism.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class HasComp {A : Type} (has_hom : HasHom A) : Type :=
  comp : forall x y z : A, (x ~> y) -> (y ~> z) -> (x ~> z).

Typeclasses Transparent HasComp.
