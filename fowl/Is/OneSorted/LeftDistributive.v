(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Multiplication.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsLDistr (A : Type)
  `(HasAdd A) `(HasMul A) : Prop :=
  l_distr : forall x y z : A, x * (y + z) = x * y + x * z.
