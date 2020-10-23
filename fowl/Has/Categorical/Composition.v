From Maniunfold.Has Require Export
  Categorical.Morphism.
From Maniunfold.ShouldHave Require Import
  Categorical.TypeNotations.

(** Composition of morphisms.
    Commonly found in semicategories. *)

Class HasComp (A : Type) `(HasHom A) : Type :=
  comp : forall x y z : A, (x --> y) -> (y --> z) -> (x --> z).

Typeclasses Transparent HasComp.
