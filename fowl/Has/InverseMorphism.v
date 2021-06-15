(** * Inverse Morphism *)

From Maniunfold.Has Require Export
  Morphism.
From Maniunfold.ShouldHave Require Import
  MorphismNotations.

Class HasInvHom (A : Type) (C : HasHom A) : Type :=
  inv_hom (x y : A) : (x --> y) -> (y --> x).

Typeclasses Transparent HasInvHom.
