(** * Inverse Morphism *)

From Maniunfold.Has Require Export
  Morphism.
From Maniunfold.ShouldHave Require Import
  MorphismNotations.

Class HasInvHom (A : Type) (HC : HasHom A) : Type :=
  inv_hom (x y : A) (a : x --> y) : y --> x.

Typeclasses Transparent HasInvHom.
