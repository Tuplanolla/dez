(** * Identity Morphism *)

From DEZ.Has Require Export
  Morphism.
From DEZ.ShouldHave Require Import
  MorphismNotations.

Class HasIdHom (A : Type) (HC : HasHom A) : Type :=
  id_hom (x : A) : x --> x.

Typeclasses Transparent HasIdHom.
