(** * Inverse Morphism *)

From DEZ.Has Require Export
  Morphism.
From DEZ.ShouldHave Require Import
  MorphismNotations.

Class HasInvHom (A : Type) (HC : HasHom A) : Type :=
  inv_hom (x y : A) (a : x --> y) : y --> x.

Typeclasses Transparent HasInvHom.
