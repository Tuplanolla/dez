(* bad *)
From Maniunfold.Has Require Export
  OneSortedAddition OneSortedMultiplication.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations.

Class IsLDistr (A : Type)
  `(HasAdd A) `(HasMul A) : Prop :=
  l_distr : forall x y z : A, x * (y + z) = x * y + x * z.
