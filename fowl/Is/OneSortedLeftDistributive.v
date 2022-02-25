(* bad *)
From DEZ.Has Require Export
  Addition Multiplication.
From DEZ.Supports Require Import
  OneSortedArithmeticNotations.

Class IsDistrL (A : Type)
  `(HasAdd A) `(HasMul A) : Prop :=
  distr_l : forall x y z : A, x * (y + z) = x * y + x * z.
