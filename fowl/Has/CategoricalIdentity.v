From Maniunfold.Has Require Export
  CategoricalMorphism.
From Maniunfold.ShouldHave Require Import
  CategoricalTypeNotations.

(** Identity morphism, unit morphism, looping arrow.
    Commonly found in categories. *)

Class HasIdt (A : Type) `(HasHom A) : Type :=
  idn : forall x : A, x --> x.

Typeclasses Transparent HasIdt.
