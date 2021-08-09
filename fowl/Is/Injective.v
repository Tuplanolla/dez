(** * Injectivity of a Function *)

From DEZ.Has Require Export
  BinaryOperation.
From DEZ.ShouldHave Require Import
  AdditiveNotations.

Class IsInj (A B : Type) (f : A -> B) : Prop :=
  inj (x y : A) (a : f x = f y) : x = y.
