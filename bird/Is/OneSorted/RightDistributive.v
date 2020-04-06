(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Multiplication.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsRDistr {A : Type}
  (A_has_add : HasAdd A) (A_has_mul : HasMul A) : Prop :=
  r_distr : forall x y z : A, (x + y) * z = x * z + y * z.
