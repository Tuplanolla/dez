(* bad *)
From Maniunfold.Has Require Export
  OneSorted.UnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class IsInj (A : Type) `(HasUnOp A) : Prop :=
  inj : forall x y : A, - x = - y -> x = y.
