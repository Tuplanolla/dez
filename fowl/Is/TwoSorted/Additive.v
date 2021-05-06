(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition Function.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsAddve (A B : Type)
  `(HasAdd A) `(HasAdd B)
  `(HasFn A B) : Prop :=
  addve : forall x y : A, fn (x + y) = fn x + fn y.
