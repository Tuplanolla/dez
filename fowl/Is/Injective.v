(** * Injectivity of a Function *)

From Maniunfold.Has Require Export
  BinaryOperation.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class IsInj (A B : Type) (f : A -> B) : Prop :=
  inj (x y : A) (a : f x = f y) : x = y.
