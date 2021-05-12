(* bad *)
From Maniunfold.Has Require Export
  OneSortedBinaryOperation OneSortedAddition OneSortedGradedMultiplication.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations OneSortedGradedArithmeticNotations.

Class IsGrdRDistr (A : Type) (P : A -> Type)
  `(HasBinOp A)
  `(forall i : A, HasAdd (P i))
  `(HasGrdMul A P) : Prop :=
  grd_r_distr : forall (i j : A) (x y : P i) (z : P j),
    (x + y)%ring * z = ((x * z)%grd_ring + (y * z)%grd_ring)%ring.
