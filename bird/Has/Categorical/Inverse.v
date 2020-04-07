From Maniunfold.Has Require Export
  Categorical.Morphism.
From Maniunfold.ShouldHave Require Import
  Categorical.TypeNotations.

(** Inverse morphism, opposite morphism, reverse arrow.
    Commonly found in groupoids. *)

Class HasInv {A : Type} (A_has_hom : HasHom A) : Type :=
  inv : forall x y : A, (x --> y) -> (y --> x).

Typeclasses Transparent HasInv.
