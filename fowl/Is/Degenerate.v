From Maniunfold.Has Require Export
  Zero One.
From Maniunfold.ShouldHave Require Import
  ArithmeticNotations.

Class IsDegen (A : Type) (Hx : HasZero A) (Hy : HasOne A) : Prop :=
  degen (a : 1 = 0) (x y : A) : x = y.
