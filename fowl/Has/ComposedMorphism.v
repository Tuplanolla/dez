(** * Composition of Morphisms *)

From Maniunfold.Has Require Export
  Morphism.
From Maniunfold.ShouldHave Require Import
  MorphismNotations.

Class HasCompHom (A : Type) (C : HasHom A) : Type :=
  comp_hom (x y z : A) : (y --> z) -> (x --> y) -> (x --> z).

Typeclasses Transparent HasCompHom.
