From Maniunfold.Has Require Export
  OneSorted.Zero OneSorted.One.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsDegen (A : Type) `(HasZero A) `(HasOne A) : Prop :=
  degen (x : A) : 1 = 0 -> x = 0.
