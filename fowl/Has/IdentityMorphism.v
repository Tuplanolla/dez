(** * Identity Morphism *)

From Maniunfold.Has Require Export
  Morphism.
From Maniunfold.ShouldHave Require Import
  MorphismNotations.

Class HasIdHom (A : Type) (C : HasHom A) : Type :=
  id_hom (x : A) : x --> x.

Typeclasses Transparent HasIdHom.
