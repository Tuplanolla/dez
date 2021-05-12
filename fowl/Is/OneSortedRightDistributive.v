(* bad *)
From Maniunfold.Has Require Export
  OneSortedAddition OneSortedMultiplication.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations.

Class IsRDistr (A : Type)
  `(HasAdd A) `(HasMul A) : Prop :=
  r_distr : forall x y z : A, (x + y) * z = x * z + y * z.
