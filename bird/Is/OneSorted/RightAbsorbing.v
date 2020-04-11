(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Zero OneSorted.Multiplication.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsRAbsorb (A : Type)
  (A_has_zero : HasZero A) (A_has_mul : HasMul A) : Prop :=
  r_absorb : forall x : A, x * 0 = 0.
