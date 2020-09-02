(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition TwoSorted.Function.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsAddve (A B : Type)
  (A_has_add : HasAdd A) (B_has_add : HasAdd B)
  (A_B_has_fn : HasFn A B) : Prop :=
  addve : forall x y : A, fn (x + y) = fn x + fn y.
