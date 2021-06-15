From Maniunfold.Has Require Export
  Action.
From Maniunfold.ShouldHave Require Import
  TwoSortedMultiplicativeNotations.

Class IsBicompat (A B C : Type)
  `(HasActL A C) `(HasActR B C) : Prop :=
  bicompat : forall (a : A) (x : C) (b : B),
    (a * (x * b)%r_mod)%l_mod = ((a * x)%l_mod * b)%r_mod.
