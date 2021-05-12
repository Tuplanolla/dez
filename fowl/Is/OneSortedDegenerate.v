From Maniunfold.Has Require Export
  OneSortedZero OneSortedOne.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations.

Class IsDegen (A : Type) `(HasZero A) `(HasOne A) : Prop :=
  degen (x : A) : 1 = 0 -> x = 0.
