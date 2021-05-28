From Maniunfold.Has Require Export
  CategoricalMorphism.
From Maniunfold.ShouldHave Require Import
  CategoricalTypeNotations.

(** Inverse morphism, opposite morphism, reverse arrow.
    Commonly found in groupoids. *)

Class HasInv (A : Type) `(HasHom A) : Type :=
  inv : forall x y : A, (x --> y) -> (y --> x).

Typeclasses Transparent HasInv.