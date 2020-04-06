(* bad *)
From Maniunfold.Has Require Export
  Categorical.Morphism.
From Maniunfold.ShouldHave Require Import
  Categorical.TypeNotations.

Class HasIdt {A : Type} (A_has_hom : HasHom A) : Type :=
  idt : forall x : A, x --> x.

Typeclasses Transparent HasIdt.
