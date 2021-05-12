(* bad *)
From Maniunfold.Has Require Export
  OneSortedUnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

Class IsInj (A : Type) `(HasUnOp A) : Prop :=
  inj : forall x y : A, - x = - y -> x = y.
