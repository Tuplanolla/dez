(* bad *)
From DEZ.Has Require Export
  BinaryOperation Addition OneSortedGradedMultiplication.
From DEZ.ShouldHave Require Import
  OneSortedArithmeticNotations OneSortedGradedArithmeticNotations.

Class IsGrdDistrR (A : Type) (P : A -> Type)
  `(HasBinOp A)
  `(forall i : A, HasAdd (P i))
  `(HasGrdMul A P) : Prop :=
  grd_distr_r : forall (i j : A) (x y : P i) (z : P j),
    (x + y)%ring * z = ((x * z)%grd_ring + (y * z)%grd_ring)%ring.
