(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Multiplication.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsRDistr (A : Type)
  `(HasAdd A) `(HasMul A) : Prop :=
  r_distr : forall x y z : A, (x + y) * z = x * z + y * z.
