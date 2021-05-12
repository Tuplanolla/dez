(* bad *)
From Maniunfold.Has Require Export
  OneSortedUnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

Class IsInvol (A : Type) `(HasUnOp A) : Prop :=
  invol : forall x : A, - (- x) = x.
