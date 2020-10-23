(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class IsIdem (A : Type) `(HasBinOp A) : Prop :=
  idem : forall x y : A, x + x = x.
