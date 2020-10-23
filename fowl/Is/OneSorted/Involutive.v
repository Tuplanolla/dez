(* bad *)
From Maniunfold.Has Require Export
  OneSorted.UnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class IsInvol (A : Type) `(HasUnOp A) : Prop :=
  invol : forall x : A, - (- x) = x.
