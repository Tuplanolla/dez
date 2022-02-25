(* bad *)
From DEZ.Has Require Export
  Addition.
From DEZ.Supports Require Import
  OneSortedArithmeticNotations.

Class IsAddve (A B : Type)
  `(HasAdd A) `(HasAdd B)
  (f : A -> B) : Prop :=
  addve : forall x y : A, f (x + y) = f x + f y.
