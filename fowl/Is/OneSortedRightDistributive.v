(* bad *)
From Maniunfold.Has Require Export
  Addition Multiplication.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations.

Class IsDistrR (A : Type)
  `(HasAdd A) `(HasMul A) : Prop :=
  distr_r : forall x y z : A, (x + y) * z = x * z + y * z.
