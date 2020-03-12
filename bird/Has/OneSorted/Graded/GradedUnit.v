From Maniunfold.Has Require Export
  Unit.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class HasGrdUn (A : Type) (P : A -> Type) {has_un : HasUn A} : Type :=
  grd_un : P 0.

Typeclasses Transparent HasGrdUn.
