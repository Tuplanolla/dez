(* bad *)
From Maniunfold.Has Require Export
  OneSortedBinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

Class IsIdem (A : Type) `(HasBinOp A) : Prop :=
  idem : forall x y : A, x + x = x.
