From Maniunfold.Has Require Export
  Morphism.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class HasIdt {A : Type} (has_hom : HasHom A) : Type :=
  idt : forall x : A, x ~> x.

Typeclasses Transparent HasIdt.
