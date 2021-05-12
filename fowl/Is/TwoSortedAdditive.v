(* bad *)
From Maniunfold.Has Require Export
  OneSortedAddition Function.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations.

Class IsAddve (A B : Type)
  `(HasAdd A) `(HasAdd B)
  `(HasFn A B) : Prop :=
  addve : forall x y : A, fn (x + y) = fn x + fn y.
