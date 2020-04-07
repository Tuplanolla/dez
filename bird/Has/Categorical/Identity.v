From Maniunfold.Has Require Export
  Categorical.Morphism.
From Maniunfold.ShouldHave Require Import
  Categorical.TypeNotations.

(** Identity morphism, unit morphism, looping arrow.
    Commonly found in categories. *)

Class HasIdt {A : Type} (A_has_hom : HasHom A) : Type :=
  idt : forall x : A, x --> x.

Typeclasses Transparent HasIdt.
