From Maniunfold.Has Require Export
  NullaryOperation.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class HasGrdNullOp {A : Type} (P : A -> Type) {has_un : HasNullOp A} : Type :=
  grd_un : P 0.

Typeclasses Transparent HasGrdNullOp.
