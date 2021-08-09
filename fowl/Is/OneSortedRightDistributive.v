(* bad *)
From DEZ.Has Require Export
  Addition Multiplication.
From DEZ.ShouldHave Require Import
  OneSortedArithmeticNotations.

Class IsDistrR (A : Type)
  `(HasAdd A) `(HasMul A) : Prop :=
  distr_r : forall x y z : A, (x + y) * z = x * z + y * z.
